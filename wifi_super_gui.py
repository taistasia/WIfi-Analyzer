#!/usr/bin/env python3
"""
wifi_super_gui.py

An extended Wi‑Fi diagnostics and monitoring application for Windows 10/11.

This tool continuously monitors the current wireless connection using built‑in
Windows commands (``netsh`` and ``ping``), logs useful telemetry to CSV and
JSONL files, and presents the results in a modern Tkinter interface with
multiple tabs.  It builds upon the original Wi‑Fi diagnostics GUI by adding
throughput testing, richer diagnostic categories, configurable settings,
notifications and scheduled reporting.

Major features include:

* **Dashboard**: real‑time badges indicating connection state, signal quality,
  latency, packet loss, roaming rate and throughput.  Miniature charts show
  the last 10 minutes of signal strength and ping latency.  Status values
  update on a configurable interval.  Green/yellow/red colours give an
  at‑a‑glance indication of health.
* **Logs**: browse recent log entries from the CSV/JSON files, filter by
  keywords or date/time range, export filtered logs to a separate file and
  open the logs in your default editor (Windows only via ``os.startfile``).
* **Channels**: histogram views of 2.4 GHz and 5 GHz channel utilisation with
  congestion warnings.  Lists the top 15 BSSIDs by signal strength.
* **Diagnostics**: runs a series of health checks on the WLAN service,
  connection quality, roaming frequency and channel plan.  Each check is
  summarised as PASS/WARN/FAIL with actionable fixes.  Issues are grouped by
  category, and clicking on an issue reveals detailed descriptions, causes,
  suggested resolutions and links to Windows tools.
* **Settings**: a dedicated tab for configuring the application.  Users can
  adjust appearance (light/dark mode and accent colour), thresholds for
  warnings and failures, dashboard layout, scan interval, ping targets,
  logging retention, notification preferences, scheduled diagnostics and
  speed‑test settings.  Changes are saved back to ``config.yaml``.
* **Speed Test**: optional throughput testing using either an HTTP download or
  ``iperf3`` if available.  Results are displayed on the dashboard and can be
  included in reports.
* **Notifications**: optional pop‑up alerts when signal strength, packet loss
  or latency exceed user‑defined thresholds or when new issues are detected.
* **Scheduled Diagnostics & Reporting**: automatically run full health
  diagnostics at a user‑defined interval.  Reports summarise recent signal
  quality, latency, speed tests and detected issues.  Reports can be
  exported as simple HTML files with embedded charts.

This script is self‑contained.  Configuration is loaded from ``config.yaml``
if present in the same directory, otherwise sensible defaults are used.  A
separate troubleshooting database may be supplied via
``troubleshooting_database.yaml``; if absent, the built‑in database is used.

Dependencies:
    * Python 3.7 or newer
    * PyYAML (``pip install pyyaml``)
    * psutil (``pip install psutil``)
    * matplotlib (``pip install matplotlib``)
    * iperf3 (optional for throughput tests; ``pip install iperf3``)

Copyright 2025.  Distributed under the MIT Licence.
"""

import base64
import csv
import io
import json
import os
import queue
import re
import subprocess
import threading
import time
import urllib.request
import zipfile
from collections import deque
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Callable

# math is used for NaN checks and dynamic axis scaling in charts
import math

# External dependencies
import psutil
import yaml

try:
    import iperf3  # optional: used for throughput tests if installed
except ImportError:
    iperf3 = None

try:
    # Optional library for native Windows notifications.  If not available,
    # notifications will fall back to Tkinter message boxes.
    from plyer import notification  # type: ignore
except ImportError:
    notification = None  # type: ignore

# Tkinter imports
import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter import ttk

# Matplotlib for charts
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

################################################################################
# Configuration Handling
################################################################################

def deep_update(d: Dict, u: Dict) -> Dict:
    """Recursively update a nested dictionary ``d`` with ``u``.

    Values in ``u`` override those in ``d``.  When both values are dicts, the
    update is performed recursively.  Returns ``d`` for convenience.
    """
    for k, v in u.items():
        if isinstance(v, dict) and isinstance(d.get(k), dict):
            deep_update(d[k], v)
        else:
            d[k] = v
    return d


def load_config() -> Dict:
    """Load configuration from ``config.yaml`` located next to this script.

    The configuration supports nested dictionaries.  If the file does not
    exist or cannot be parsed, defaults are used.  Users should wrap
    Windows paths in single quotes or escape backslashes when editing
    ``config.yaml``.

    :returns: A dict containing configuration values.
    """
    # Default settings
    defaults: Dict = {
        "log_dir": "logs",
        "scan_interval": 10,
        "ping_targets": {
            "gateway": None,  # auto‑detect by default
            "remote": "8.8.8.8",
        },
        "ping_count": 4,
        "log_retention_days": 14,
        "max_log_mb": 512,
        # Appearance settings
        "appearance": {
            "theme": "light",  # options: light, dark
            "accent_color": "#0066cc",
            "font_size": 10,
        },
        # Dashboard element toggles
        "dashboard_layout": {
            "show_signal": True,
            "show_latency": True,
            "show_roams": True,
            "show_throughput": True,
            "show_charts": True,
        },
        # Thresholds for warnings/fails (percentages and milliseconds)
        "thresholds": {
            "signal_warn": 55,
            "signal_fail": 35,
            "loss_warn": 10,
            "loss_fail": 20,
            "latency_warn": 150,
            "latency_fail": 300,
        },
        # Notifications
        "notifications": {
            "enabled": True,
            "signal_threshold": 35,
            "loss_threshold": 20,
            "latency_threshold": 200,
            "channels": ["popup"],  # supported: popup (Tk), plyer, email, slack
        },
        # Speed test settings
        "speed_test": {
            "enabled": False,
            "type": "http",  # http or iperf3
            "url": "http://speedtest.tele2.net/1MB.zip",
            "iperf3_server": "",
            "iperf3_port": 5201,
            "duration": 10,  # seconds for iperf3
        },
        # Scheduled diagnostics
        "scheduled_diagnostics": {
            "enabled": False,
            "interval_hours": 12,
        },
    }
    cfg_path = Path(__file__).with_name("config.yaml")
    if cfg_path.exists():
        try:
            with cfg_path.open("r", encoding="utf-8") as f:
                user_cfg: Dict = yaml.safe_load(f) or {}
            deep_update(defaults, user_cfg)
        except yaml.YAMLError as e:
            print(f"Could not parse config.yaml: {e}.\n"
                  "Ensure that any Windows paths are either wrapped in single quotes or use double backslashes.")
        except Exception as e:
            print(f"Could not read config.yaml: {e}")
    # Normalise log_dir to absolute path
    defaults["log_dir"] = str((Path(__file__).parent / defaults["log_dir"]).resolve())
    return defaults


def save_config(cfg: Dict) -> None:
    """Persist the configuration to ``config.yaml`` next to this script."""
    cfg_path = Path(__file__).with_name("config.yaml")
    try:
        with cfg_path.open("w", encoding="utf-8") as f:
            yaml.safe_dump(cfg, f, sort_keys=False)
    except Exception as e:
        print(f"Failed to save config: {e}")


################################################################################
# Troubleshooting Database Handling
################################################################################

def load_troubleshooting_database() -> Dict[str, Dict[str, object]]:
    """Load a troubleshooting database from ``troubleshooting_database.yaml``.

    If the file exists next to this script, parse it and return the content.
    Otherwise fall back to the built‑in dictionary defined below.
    Each entry must include at least ``title``, ``description``, ``causes``,
    ``resolutions``, ``links`` and ``category``.
    """
    db_path = Path(__file__).with_name("troubleshooting_database.yaml")
    if db_path.exists():
        try:
            with db_path.open("r", encoding="utf-8") as f:
                data = yaml.safe_load(f)
            # Basic validation: ensure expected fields exist
            if isinstance(data, dict):
                return data
        except Exception as e:
            print(f"Failed to load troubleshooting database: {e}")
    # Fallback to built‑in database
    return BUILTIN_TROUBLESHOOTING_DATABASE


################################################################################
# Built‑in Troubleshooting Database
################################################################################

# The built‑in database defines known Wi‑Fi issues.  Each entry must include
# ``title``, ``description``, ``causes``, ``resolutions``, ``links`` and
# ``category`` (for grouping).  The keys act as internal identifiers that
# diagnostics routines refer to when raising issues.  If you add a new issue,
# update the heuristics in ``run_health_check`` or ``_analyse_logs`` to map
# conditions to these IDs.
BUILTIN_TROUBLESHOOTING_DATABASE: Dict[str, Dict[str, object]] = {
    "wlan_service_not_running": {
        "title": "WLAN AutoConfig Service Not Running",
        "description": "The Windows service responsible for wireless configuration (WLAN AutoConfig) is not running. Without this service the Wi‑Fi adapter cannot connect to networks.",
        "causes": [
            "The service was manually stopped or disabled.",
            "A recent Windows update or system change affected the service configuration.",
        ],
        "resolutions": [
            "Open Services (services.msc) and locate 'WLAN AutoConfig'.",
            "Start the service and set its Startup Type to 'Automatic'.",
            "Reboot the computer if the service fails to start.",
        ],
        "links": [("Open Services", "services.msc")],
        "category": "Service & driver problems",
    },
    "adapter_disconnected": {
        "title": "Adapter Disconnected",
        "description": "The Wi‑Fi adapter is disconnected from any network. Monitoring cannot gather stats until a connection is established.",
        "causes": [
            "Wi‑Fi is turned off or airplane mode is enabled.",
            "No saved networks or incorrect credentials.",
            "Driver or hardware issues preventing the adapter from connecting."
        ],
        "resolutions": [
            "Ensure Wi‑Fi is enabled (toggle the wireless switch or use the network icon).",
            "Select and connect to a known network using Windows networking settings.",
            "Update or reinstall the Wi‑Fi driver via Device Manager."
        ],
        "links": [("Network Settings", "ms-settings:network-wifi"), ("Device Manager", "devmgmt.msc")],
        "category": "Service & driver problems",
    },
    "weak_signal": {
        "title": "Weak Signal Strength",
        "description": "The average received signal strength is below the recommended threshold (<35%). Low signal levels can cause slow speeds, dropouts and high error rates.",
        "causes": [
            "The device is too far from the access point.",
            "Physical obstructions such as walls or metal surfaces.",
            "Interference from other electronic devices or neighbouring networks."
        ],
        "resolutions": [
            "Move closer to the Wi‑Fi access point.",
            "Reposition the router away from walls and elevate it to reduce obstructions.",
            "Change the Wi‑Fi channel or band (e.g. switch to 5 GHz) to avoid interference.",
            "Consider adding a Wi‑Fi extender or additional access point."
        ],
        "links": [],
        "category": "Signal & interference",
    },
    "moderate_signal": {
        "title": "Moderate Signal Strength",
        "description": "The signal strength is acceptable but could be improved (35–55%).",
        "causes": [
            "Distance from the access point.",
            "Partial obstructions or moderate interference.",
        ],
        "resolutions": [
            "Reposition the device or router for a clearer line of sight.",
            "Select a less crowded channel or use the 5 GHz band if available.",
        ],
        "links": [],
        "category": "Signal & interference",
    },
    "low_average_signal_log": {
        "title": "Low Average Signal (Historical)",
        "description": "Historical log analysis shows that the average signal strength over time is low.",
        "causes": [
            "Persistent weak signal conditions or temporary outages.",
            "Roaming between APs with varying coverage.",
        ],
        "resolutions": [
            "Follow the steps for improving weak signal strength.",
            "Analyse roaming pattern and adjust AP placement."
        ],
        "links": [],
        "category": "Signal & interference",
    },
    "moderate_average_signal_log": {
        "title": "Moderate Average Signal (Historical)",
        "description": "Historical logs indicate the signal strength is moderate on average.",
        "causes": [
            "The device is sometimes far from the AP or experiences occasional interference.",
        ],
        "resolutions": [
            "Optimise the AP placement and evaluate use of the 5 GHz band."
        ],
        "links": [],
        "category": "Signal & interference",
    },
    "gateway_packet_loss": {
        "title": "High Packet Loss to Gateway",
        "description": "Frequent high packet loss to the local gateway indicates local network issues.",
        "causes": [
            "Severe RF interference on the current channel.",
            "The access point is overloaded or misconfigured.",
            "Physical obstructions or weak signal."
        ],
        "resolutions": [
            "Change to a less congested channel or band.",
            "Reduce network load or update router firmware.",
            "Reposition the AP and client devices."
        ],
        "links": [],
        "category": "Network performance",
    },
    "internet_packet_loss": {
        "title": "High Packet Loss to Internet",
        "description": "High packet loss when pinging an external host points to upstream or ISP problems.",
        "causes": [
            "Congested or faulty WAN link.",
            "ISP routing issues or maintenance.",
        ],
        "resolutions": [
            "Power cycle the modem and router.",
            "Check with your ISP for outages or performance issues.",
            "Test with alternative remote hosts to confirm."
        ],
        "links": [],
        "category": "Network performance",
    },
    "gateway_high_latency": {
        "title": "High Gateway Latency",
        "description": "Ping responses from the local gateway are slower than expected, suggesting local congestion or wireless retransmissions.",
        "causes": [
            "Too many clients on the AP.",
            "RF interference requiring multiple retransmissions.",
            "Overloaded router CPU."
        ],
        "resolutions": [
            "Reduce the number of active Wi‑Fi devices.",
            "Switch to a less congested channel.",
            "Update router firmware and ensure QoS settings are appropriate."
        ],
        "links": [],
        "category": "Network performance",
    },
    "internet_high_latency": {
        "title": "High Internet Latency",
        "description": "High latency to external hosts may indicate upstream congestion or ISP routing problems.",
        "causes": [
            "Internet service provider congestion or routing changes.",
            "Excessive WAN load from downloads or streaming.",
        ],
        "resolutions": [
            "Pause large downloads or streaming.",
            "Contact your ISP if the issue persists.",
            "Run a speed test and traceroute to identify bottlenecks."
        ],
        "links": [],
        "category": "Network performance",
    },
    "excessive_roaming": {
        "title": "Excessive Roaming",
        "description": "Your device is roaming between access points frequently, indicating overlapping coverage or aggressive roaming settings.",
        "causes": [
            "Access points placed too close together.",
            "High transmit power causing cells to overlap.",
            "Client roaming algorithm is too aggressive.",
        ],
        "resolutions": [
            "Reduce AP transmit power or adjust placement to limit overlap.",
            "Enable 802.11k/v/r fast‑roaming features on APs and clients.",
            "Check the client device roaming aggressiveness setting."
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
    "moderate_roaming": {
        "title": "Moderate Roaming",
        "description": "The device roams a moderate number of times per hour.",
        "causes": [
            "AP cells slightly overlapping.",
            "Normal behaviour in multi‑AP environments."
        ],
        "resolutions": [
            "Monitor if roaming becomes excessive; adjust AP placement if needed."
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
    "bad_channel_plan": {
        "title": "Suboptimal Channel Plan",
        "description": "One or more APs on 2.4 GHz are using channels other than 1, 6, or 11.",
        "causes": [
            "APs configured to Auto channel mode that selected a non‑standard channel.",
            "Manual misconfiguration or older hardware unable to change channels."
        ],
        "resolutions": [
            "Set your 2.4 GHz APs to channels 1, 6 or 11 only.",
            "Use 20 MHz channel width to reduce overlap."
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
    "crowded_channel": {
        "title": "Crowded 2.4 GHz Channel",
        "description": "There are many APs on or adjacent to the current 2.4 GHz channel, causing congestion.",
        "causes": [
            "Dense network environment with overlapping channels.",
            "Neighbours using the same or adjacent channels."
        ],
        "resolutions": [
            "Switch to a less crowded channel on 2.4 GHz (1, 6 or 11).",
            "Use the 5 GHz band where possible.",
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
    "frequent_disconnections": {
        "title": "Frequent Disconnections",
        "description": "Historical logs show that the device disconnects from Wi‑Fi often.",
        "causes": [
            "Faulty or outdated drivers.",
            "Power management settings causing the adapter to sleep.",
            "Weak signal or interference leading to dropped connections."
        ],
        "resolutions": [
            "Update network drivers from the device manufacturer.",
            "Disable power saving on the Wi‑Fi adapter in Device Manager.",
            "Improve signal quality by following weak signal recommendations."
        ],
        "links": [("Device Manager", "devmgmt.msc")],
        "category": "Service & driver problems",
    },
    "many_roam_events": {
        "title": "Many Roam Events (Historical)",
        "description": "The historical roam log indicates that the device roams frequently between APs.",
        "causes": [
            "Similar to excessive roaming: overlapping APs and aggressive roaming settings.",
        ],
        "resolutions": [
            "See the solutions for excessive roaming."
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
    # Additional common issues
    "power_management_sleep": {
        "title": "Power Management Causing Adapter Sleep",
        "description": "The Wi‑Fi adapter is entering sleep mode due to power management, resulting in disconnections or degraded performance.",
        "causes": [
            "Power saving mode enabled on the adapter or system.",
            "Operating system settings configured for maximum power saving."
        ],
        "resolutions": [
            "Open Device Manager → network adapter → Properties → Power Management. Uncheck 'Allow the computer to turn off this device to save power'.",
            "Change Windows power plan to 'High Performance' or adjust advanced power settings to disable wireless power saving."
        ],
        "links": [("Device Manager", "devmgmt.msc"), ("Power Options", "powercfg.cpl")],
        "category": "Service & driver problems",
    },
    "driver_outdated": {
        "title": "Outdated or Faulty Driver",
        "description": "The installed Wi‑Fi driver is outdated or has known stability issues, causing performance problems or disconnects.",
        "causes": [
            "Driver version provided by Windows Update is outdated.",
            "Corrupted or incomplete driver installation."
        ],
        "resolutions": [
            "Download the latest driver from the device manufacturer's website.",
            "Perform a clean installation: uninstall the old driver, reboot and install the new driver.",
        ],
        "links": [("Device Manager", "devmgmt.msc")],
        "category": "Service & driver problems",
    },
    "security_mismatch": {
        "title": "Security Mismatch (WPA2 vs WPA3)",
        "description": "Authentication failures or intermittent connectivity can occur if the AP and client use incompatible security settings (e.g. WPA2 vs WPA3).",
        "causes": [
            "The AP is configured for WPA3 only while the client supports only WPA2, or vice versa.",
            "Mixed mode settings cause negotiation issues."
        ],
        "resolutions": [
            "Ensure both AP and client support the same security modes.",
            "Configure AP to allow mixed WPA2/WPA3 modes or adjust client settings accordingly.",
            "Update firmware and drivers to add WPA3 support if available."
        ],
        "links": [],
        "category": "Signal & interference",
    },
    "channel_width_problem": {
        "title": "Channel Width Mismatch",
        "description": "The AP uses a channel width (e.g. 40 MHz or 80 MHz) that is too wide for the environment, causing interference and performance issues.",
        "causes": [
            "Auto channel width selection chooses 40 MHz on 2.4 GHz or 80 MHz on 5 GHz in a crowded environment.",
            "Manual configuration set an unsupported width on the client or AP."
        ],
        "resolutions": [
            "Set the AP channel width to 20 MHz on 2.4 GHz and 40/80 MHz on 5 GHz depending on congestion.",
            "Match the client's channel width settings to the AP."
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
    "dfs_radar_events": {
        "title": "DFS Radar Events",
        "description": "On 5 GHz bands, Dynamic Frequency Selection (DFS) channels may be vacated when a radar signal is detected, causing the AP to switch channels unexpectedly.",
        "causes": [
            "Operating on DFS channels (52–64 or 100–144).",
            "Nearby weather or military radar forcing channel change."
        ],
        "resolutions": [
            "Avoid DFS channels if you experience frequent disconnects when the AP changes channels.",
            "Monitor the AP logs for DFS events and choose a non‑DFS channel if possible."
        ],
        "links": [],
        "category": "Roaming & channel plan",
    },
}

################################################################################
# Utility Functions for Windows Network Commands
################################################################################

def run_command(cmd: str, timeout: int = 8) -> str:
    """Run a shell command and return its output as a string.

    :param cmd: Command line to execute.
    :param timeout: Timeout in seconds.
    :returns: Output string (stdout) or empty string on error.
    """
    try:
        return subprocess.run(cmd, shell=True, text=True,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL,
                              timeout=timeout).stdout
    except Exception:
        return ""


def autodetect_gateway() -> Optional[str]:
    """Attempt to determine the default IPv4 gateway using PowerShell.

    Returns the IP address of the default gateway or ``None`` if detection
    fails.  Uses the same logic as the original tool.
    """
    # Use PowerShell Get-NetRoute to find lowest metric default route
    cmd = (r'powershell -NoProfile -Command "(Get-NetRoute -DestinationPrefix '
           r'0.0.0.0/0 | Sort-Object RouteMetric,InterfaceMetric | '
           r'Select-Object -First 1).NextHop"')
    gw = run_command(cmd, timeout=6).strip()
    if gw:
        return gw
    # Fallback: parse 'route print'
    rp = run_command("route print 0.0.0.0", timeout=6)
    for line in rp.splitlines():
        if "0.0.0.0" in line and "." in line:
            parts = [p for p in line.split() if p.count(".") == 3]
            if len(parts) >= 2:
                return parts[1]
    return None


def parse_netsh_interfaces(out: str) -> Dict[str, str]:
    """Parse the output of ``netsh wlan show interfaces`` into a dict."""
    info = {
        "state": "",
        "ssid": "",
        "bssid": "",
        "signal_pct": "",
        "radio_type": "",
        "receive_rate": "",
        "transmit_rate": "",
        "channel": "",
        "auth": "",
    }
    for raw in out.splitlines():
        line = raw.strip()
        if line.startswith("State"):
            info["state"] = line.split(" ", 1)[-1].strip()
        elif re.match(r"^SSID\s*:", line) and not line.lower().startswith("ssid name"):
            info["ssid"] = line.split(":", 1)[1].strip()
        elif line.startswith("BSSID"):
            info["bssid"] = line.split(":", 1)[1].strip()
        elif line.startswith("Signal"):
            info["signal_pct"] = line.split(":", 1)[1].strip()
        elif line.startswith("Channel"):
            info["channel"] = line.split(":", 1)[1].strip()
        elif line.startswith("Radio type"):
            info["radio_type"] = line.split(":", 1)[1].strip()
        elif line.startswith("Receive rate"):
            info["receive_rate"] = line.split(":", 1)[1].strip()
        elif line.startswith("Transmit rate"):
            info["transmit_rate"] = line.split(":", 1)[1].strip()
        elif line.startswith("Authentication"):
            info["auth"] = line.split(":", 1)[1].strip()
    return info


def parse_netsh_scan(out: str) -> List[Dict[str, object]]:
    """Parse the output of ``netsh wlan show networks mode=bssid``.

    Returns a list of dicts each representing an SSID with its BSSIDs.
    Each dict has fields: ``ssid`` and ``bssids`` (a list of dicts with
    ``bssid``, ``signal``, ``radio`` and ``channel``).
    """
    aps = []
    cur: Optional[Dict[str, object]] = None
    for raw in out.splitlines():
        s = raw.strip()
        if s.startswith("SSID "):
            if cur:
                aps.append(cur)
            cur = {"ssid": s.split(":", 1)[1].strip(), "bssids": []}
        elif s.startswith("BSSID "):
            if cur is not None:
                cur["bssids"].append({"bssid": s.split(":", 1)[1].strip(), "signal": "", "radio": "", "channel": ""})
        elif s.startswith("Signal") and cur and cur["bssids"]:
            cur["bssids"][-1]["signal"] = s.split(":", 1)[1].strip()
        elif s.startswith("Radio type") and cur and cur["bssids"]:
            cur["bssids"][-1]["radio"] = s.split(":", 1)[1].strip()
        elif s.startswith("Channel") and cur and cur["bssids"]:
            cur["bssids"][-1]["channel"] = s.split(":", 1)[1].strip()
    if cur:
        aps.append(cur)
    return aps


def ping_host(host: str, count: int = 4) -> Tuple[Optional[float], Optional[int]]:
    """Ping a host and return (average_latency_ms, packet_loss_percent).

    Uses the Windows ``ping`` command.  Returns ``(None, None)`` on error.
    """
    if not host:
        return None, None
    out = run_command(f"ping -n {count} {host}", timeout=10)
    if not out:
        return None, None
    loss = None
    avg = None
    for line in out.splitlines():
        if "Lost =" in line and "(" in line:
            # Extract packet loss
            try:
                loss = int(line.split("(")[1].split("%", 1)[0])
            except Exception:
                pass
        if "Average =" in line:
            try:
                avg = int(line.split("Average =")[-1].replace("ms", "").strip())
            except Exception:
                pass
    return avg, loss


def band_for_channel(ch_str: str) -> str:
    """Return a band label (2.4, 5, 6, ?) based on channel number string."""
    try:
        ch = int(ch_str)
    except Exception:
        return "?"
    if ch <= 14:
        return "2.4"
    if 32 <= ch <= 177:
        return "5"
    if ch >= 180:
        return "6"
    return "?"


################################################################################
# Speed Test Implementation
################################################################################

def http_speed_test(url: str) -> Optional[float]:
    """Download a file from ``url`` and return the download speed in Mbps.

    This function performs a simple HTTP GET request to download a file.  It
    measures the elapsed time and the total number of bytes received.  The
    returned speed is in megabits per second.  Returns ``None`` on error.
    """
    try:
        start = time.perf_counter()
        with urllib.request.urlopen(url, timeout=15) as response:
            data = response.read()
        elapsed = time.perf_counter() - start
        if elapsed <= 0:
            return None
        size_bytes = len(data)
        speed_mbps = (size_bytes * 8) / (elapsed * 1_000_000)
        return speed_mbps
    except Exception:
        return None


def iperf3_speed_test(server: str, port: int, duration: int = 10) -> Optional[float]:
    """Perform a throughput test using iperf3 if available.

    The function connects to an iperf3 server and returns the measured
    throughput in Mbps.  Requires the ``iperf3`` Python module.  Returns
    ``None`` if the module is unavailable or on error.
    """
    if iperf3 is None:
        return None
    try:
        client = iperf3.Client()
        client.server_hostname = server
        client.port = port
        client.duration = duration
        result = client.run()
        if result is not None and hasattr(result, 'received_Mbps'):
            return float(result.received_Mbps)
    except Exception:
        pass
    return None


################################################################################
# Logging and Log Rotation
################################################################################

def rotate_log(path: Path, retention_days: int, max_mb: float) -> None:
    """Rotate and trim log files based on age and total folder size.

    :param path: The directory containing log files.
    :param retention_days: Days to keep old logs.
    :param max_mb: Maximum folder size in megabytes.
    """
    if not path.exists():
        return
    # Remove files older than retention_days
    cutoff = datetime.now(timezone.utc) - timedelta(days=retention_days)
    for f in path.glob("*.zip"):
        try:
            stamp = f.stem.split("_")[-1]
            dt = datetime.strptime(stamp, "%Y%m%d").replace(tzinfo=timezone.utc)
            if dt < cutoff.replace(hour=0, minute=0, second=0, microsecond=0):
                f.unlink(missing_ok=True)
        except Exception:
            pass
    # If folder exceeds max_mb, delete oldest files
    def folder_size_mb(p: Path) -> float:
        total = 0
        for file in p.rglob("*"):
            if file.is_file():
                total += file.stat().st_size
        return total / (1024 * 1024)
    while folder_size_mb(path) > max_mb:
        files = sorted([p for p in path.glob("*") if p.is_file()], key=lambda p: p.stat().st_mtime)
        if files:
            files[0].unlink(missing_ok=True)
        else:
            break


################################################################################
# Background Worker Threads
################################################################################

class MonitorThread(threading.Thread):
    """Background thread for monitoring Wi‑Fi statistics and logging.

    Samples the current wireless interface using ``netsh`` commands and ICMP
    pings at a user‑configured interval.  Maintains rolling buffers for
    real‑time charts, writes log entries to CSV/JSONL, rotates logs, detects
    roam events, triggers notifications and performs periodic health checks.

    Results are delivered to a callback (usually the GUI) as a dictionary
    containing summary statistics.
    """
    def __init__(self, config: Dict, db: Dict[str, Dict[str, object]], summary_callback: Callable[[Dict], None]):
        super().__init__(daemon=True)
        self.cfg = config
        self.db = db
        self.summary_callback = summary_callback
        self.stop_event = threading.Event()
        # Log paths
        self.log_dir = Path(self.cfg["log_dir"])
        self.log_dir.mkdir(parents=True, exist_ok=True)
        self.csv_path = self.log_dir / "wifi_log.csv"
        self.jsonl_path = self.log_dir / "wifi_log.jsonl"
        self.roam_path = self.log_dir / "roaming_events.csv"
        # Initialising logs
        if not self.csv_path.exists():
            with self.csv_path.open("w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow([
                    "ts", "state", "ssid", "bssid", "signal_pct", "channel", "radio_type",
                    "ping_gateway_avg", "ping_gateway_loss", "ping_remote_avg", "ping_remote_loss",
                    "download_mbps"
                ])
        if not self.roam_path.exists():
            with self.roam_path.open("w", newline="", encoding="utf-8") as f:
                csv.writer(f).writerow(["ts", "ssid", "old_bssid", "new_bssid", "old_signal", "new_signal"])
        # Rolling buffers for charts
        max_samples = max(60, int(600 / max(1, self.cfg["scan_interval"])))
        self.buf_signal = deque(maxlen=max_samples)
        self.buf_ping_gw = deque(maxlen=max_samples)
        self.buf_ping_rem = deque(maxlen=max_samples)
        self.buf_throughput = deque(maxlen=max_samples)
        self.buf_ts = deque(maxlen=max_samples)
        # State for roaming detection
        self.prev_bssid: Optional[str] = None
        self.prev_signal: Optional[str] = None
        # Last speed test result
        self.last_speed_test: Optional[float] = None
        # Last health check timestamp
        self.last_diagnostics_time: Optional[datetime] = None
        # Start scheduled diagnostics timer if enabled
        self.scheduled_timer: Optional[threading.Timer] = None
        if self.cfg.get("scheduled_diagnostics", {}).get("enabled"):
            interval_h = self.cfg["scheduled_diagnostics"].get("interval_hours", 12)
            self._schedule_diagnostics(interval_h * 3600)

    def run(self) -> None:
        """Main loop: sample Wi‑Fi statistics until stopped."""
        # Determine gateway to ping
        gw = self.cfg["ping_targets"].get("gateway") or autodetect_gateway()
        remote = self.cfg["ping_targets"].get("remote")
        scan_interval = self.cfg["scan_interval"]
        ping_count = self.cfg["ping_count"]
        retention_days = self.cfg.get("log_retention_days", 14)
        max_mb = float(self.cfg.get("max_log_mb", 512))
        while not self.stop_event.is_set():
            start_ts = datetime.now(timezone.utc)
            # Sample netsh interfaces
            intf_out = run_command("netsh wlan show interfaces")
            intf_info = parse_netsh_interfaces(intf_out)
            # Sample nearby networks (optional; used by Channels tab)
            scan_out = run_command("netsh wlan show networks mode=bssid")
            scan_list = parse_netsh_scan(scan_out)
            # Ping targets
            ping_gw_avg, ping_gw_loss = ping_host(gw, ping_count) if gw else (None, None)
            ping_rem_avg, ping_rem_loss = ping_host(remote, ping_count) if remote else (None, None)
            # Throughput (if last speed test result is available)
            throughput = self.last_speed_test
            # Determine roaming events
            cur_bssid = intf_info.get("bssid")
            cur_signal = intf_info.get("signal_pct")
            if intf_info.get("ssid") and cur_bssid:
                if self.prev_bssid and self.prev_bssid != cur_bssid:
                    # Log roam event
                    with self.roam_path.open("a", newline="", encoding="utf-8") as f:
                        csv.writer(f).writerow([
                            start_ts.isoformat(), intf_info.get("ssid"), self.prev_bssid, cur_bssid,
                            self.prev_signal or "", cur_signal or ""
                        ])
                self.prev_bssid = cur_bssid
                self.prev_signal = cur_signal
            # Update rolling buffers
            try:
                sig = float(cur_signal.replace("%", "")) if cur_signal else float('nan')
            except Exception:
                sig = float('nan')
            self.buf_signal.append(sig)
            self.buf_ping_gw.append(ping_gw_avg if ping_gw_avg is not None else float('nan'))
            self.buf_ping_rem.append(ping_rem_avg if ping_rem_avg is not None else float('nan'))
            self.buf_throughput.append(throughput if throughput is not None else float('nan'))
            self.buf_ts.append(start_ts)
            # Write log entry
            with self.csv_path.open("a", newline="", encoding="utf-8") as cf:
                csv.writer(cf).writerow([
                    start_ts.isoformat(), intf_info.get("state"), intf_info.get("ssid"), cur_bssid,
                    cur_signal, intf_info.get("channel"), intf_info.get("radio_type"),
                    ping_gw_avg if ping_gw_avg is not None else "", ping_gw_loss if ping_gw_loss is not None else "",
                    ping_rem_avg if ping_rem_avg is not None else "", ping_rem_loss if ping_rem_loss is not None else "",
                    throughput if throughput is not None else ""
                ])
            # Also write JSONL for extended details
            with self.jsonl_path.open("a", encoding="utf-8") as jf:
                jf.write(json.dumps({
                    "ts": start_ts.isoformat(),
                    "interface": intf_info,
                    "scan": scan_list,
                    "ping_gateway": {"avg": ping_gw_avg, "loss": ping_gw_loss},
                    "ping_remote": {"avg": ping_rem_avg, "loss": ping_rem_loss},
                    "throughput": throughput,
                }) + "\n")
            # Rotate logs periodically (once per day) and trim folder size
            if start_ts.time().hour == 0 and start_ts.time().minute == 0:
                rotate_log(self.log_dir, retention_days, max_mb)
            # Notifications based on thresholds
            self._check_thresholds(sig, ping_gw_loss, ping_rem_loss, ping_gw_avg, ping_rem_avg)
            # Deliver summary to GUI
            summary = {
                "timestamp": start_ts,
                "interface": intf_info,
                "ping_gateway": {"avg": ping_gw_avg, "loss": ping_gw_loss},
                "ping_remote": {"avg": ping_rem_avg, "loss": ping_rem_loss},
                "throughput": throughput,
                "signal_buffer": list(self.buf_signal),
                "ping_gw_buffer": list(self.buf_ping_gw),
                "ping_rem_buffer": list(self.buf_ping_rem),
                "throughput_buffer": list(self.buf_throughput),
                "ts_buffer": list(self.buf_ts),
                "scan_flat": self._flatten_scan(scan_list),
            }
            self.summary_callback(summary)
            # Sleep until next sample or until stop
            for _ in range(int(self.cfg["scan_interval"] * 10)):
                if self.stop_event.is_set():
                    break
                time.sleep(0.1)
        # Clean up scheduled timer on exit
        if self.scheduled_timer:
            self.scheduled_timer.cancel()

    def stop(self) -> None:
        self.stop_event.set()

    def _flatten_scan(self, scan: List[Dict[str, object]]) -> List[Dict[str, object]]:
        """Flatten the scan list into a simple list of BSSID entries."""
        flat = []
        for ap in scan:
            ssid = ap.get("ssid", "")
            for b in ap.get("bssids", []):
                ch = b.get("channel", "")
                sig = b.get("signal", "")
                sig_pct = sig.replace("%", "").strip() if "%" in sig else sig
                flat.append({
                    "ssid": ssid,
                    "bssid": b.get("bssid", ""),
                    "channel": ch,
                    "band": band_for_channel(ch),
                    "signal_pct": sig_pct,
                })
        # Sort by descending signal
        def keyfn(x):
            try:
                return -int(str(x["signal_pct"]))
            except Exception:
                return 0
        return sorted(flat, key=keyfn)

    def _check_thresholds(self, sig: float, gw_loss: Optional[int], rem_loss: Optional[int], gw_latency: Optional[float], rem_latency: Optional[float]) -> None:
        """Trigger notifications when thresholds are exceeded."""
        if not self.cfg.get("notifications", {}).get("enabled"):
            return
        thresholds = self.cfg.get("notifications", {})
        def do_notify(msg):
            # Use plyer notification if available and configured, else fallback to Tk
            channels = thresholds.get("channels", [])
            if "plyer" in channels and notification is not None:
                try:
                    notification.notify(title="Wi‑Fi Diagnostics", message=msg)
                except Exception:
                    pass
            if "popup" in channels:
                try:
                    # Use non‑blocking pop‑up; schedule in main thread via callback
                    # Here we simply print to console; GUI will handle notifications separately
                    print(f"NOTIFICATION: {msg}")
                except Exception:
                    pass
        # Signal threshold
        if sig is not None and not (sig != sig) and sig < thresholds.get("signal_threshold", 35):
            do_notify(f"Signal strength low: {sig:.0f}%")
        # Loss thresholds
        if gw_loss is not None and gw_loss > thresholds.get("loss_threshold", 20):
            do_notify(f"Gateway packet loss high: {gw_loss}%")
        if rem_loss is not None and rem_loss > thresholds.get("loss_threshold", 20):
            do_notify(f"Internet packet loss high: {rem_loss}%")
        # Latency thresholds
        if gw_latency is not None and gw_latency > thresholds.get("latency_threshold", 200):
            do_notify(f"Gateway latency high: {gw_latency} ms")
        if rem_latency is not None and rem_latency > thresholds.get("latency_threshold", 200):
            do_notify(f"Internet latency high: {rem_latency} ms")

    def _schedule_diagnostics(self, delay_seconds: float) -> None:
        """Schedule a full health check to run after ``delay_seconds``."""
        if self.scheduled_timer:
            self.scheduled_timer.cancel()
        def run_and_reschedule():
            if self.stop_event.is_set():
                return
            # Create a minimal summary for health check (will be run by GUI)
            if hasattr(self, 'gui_run_health_check'):
                try:
                    self.gui_run_health_check()
                except Exception:
                    pass
            # Reschedule next run
            self._schedule_diagnostics(delay_seconds)
        self.scheduled_timer = threading.Timer(delay_seconds, run_and_reschedule)
        self.scheduled_timer.daemon = True
        self.scheduled_timer.start()


################################################################################
# GUI Application
################################################################################

class WiFiGUI(tk.Tk):
    """Main Tkinter application for Wi‑Fi diagnostics.

    Provides tabs for Dashboard, Logs, Channels, Diagnostics and Settings.  It
    communicates with the ``MonitorThread`` for real‑time telemetry and
    diagnostics.  It also manages speed tests, notifications, scheduled
    diagnostics and report generation.  Settings can be adjusted and saved
    through the Settings tab.
    """
    def __init__(self, config: Dict, database: Dict[str, Dict[str, object]]):
        super().__init__()
        self.title("Wi‑Fi Diagnostics")
        self.config = config
        self.db = database
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        # Configure a reasonable default window size and allow the user to
        # resize freely.  Assign row/column weights on the root so child
        # widgets will expand when the window is resized.  These settings help
        # charts, tables and badges grow and shrink gracefully without being
        # clipped.
        self.geometry("1080x720")
        self.minsize(860, 600)
        self.rowconfigure(0, weight=1)
        self.columnconfigure(0, weight=1)
        # Set up style and theme based on config
        self.style = ttk.Style()
        try:
            # Use built‑in Windows Vista theme if available
            self.style.theme_use("vista")
        except Exception:
            pass
        # Configure default colours for issue severities before applying the theme.
        # These are used by _apply_theme() to set badge styles. Define them early so the
        # attribute exists when _apply_theme is called.  Colours can later be customised
        # via the Settings tab if desired.
        self.issue_sev_colors = {
            "PASS": "#10b981",    # green
            "INFO": "#3b82f6",    # blue
            "WARN": "#f59e0b",    # amber
            "FAIL": "#ef4444",    # red
        }
        # Apply the selected theme and colours.  This call must come after issue_sev_colors
        # has been initialised.
        self._apply_theme()
        # Create notebook and tabs
        self.notebook = ttk.Notebook(self)
        # Use grid instead of pack so the notebook expands to fill the root
        # window.  The root already has row/column weights set above.  When
        # the window is resized, the notebook will resize as well.
        self.notebook.grid(row=0, column=0, sticky="nsew")
        # Dashboard tab
        self.tab_dashboard = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_dashboard, text="Dashboard")
        # Logs tab
        self.tab_logs = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_logs, text="Logs")
        # Channels tab
        self.tab_channels = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_channels, text="Channels")
        # Diagnostics tab
        self.tab_diag = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_diag, text="Diagnostics")
        # Settings tab
        self.tab_settings = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_settings, text="Settings")
        # Diagnostics results storage
        self.current_issues: List[Tuple[str, str]] = []  # list of (severity, issue_id)
        # Category and severity filters
        # NOTE: these variables must be defined before building the diagnostics tab,
        # because _build_diagnostics_tab references them when constructing the
        # filter dropdowns.  Defining them here ensures they exist when the
        # diagnostics tab is built.  Otherwise, accessing these attributes during
        # tab construction will raise an AttributeError.
        self.diag_filter_category = tk.StringVar(value="All")
        self.diag_filter_severity = tk.StringVar(value="All")

        # Build UI for each tab
        self._build_dashboard()
        self._build_logs_tab()
        self._build_channels_tab()
        self._build_diagnostics_tab()
        self._build_settings_tab()
        
        # Initialise monitor thread
        self.monitor = MonitorThread(self.config, self.db, self._on_monitor_summary)
        # Expose run_health_check to monitor (for scheduled diagnostics)
        setattr(self.monitor, 'gui_run_health_check', self.run_health_check)
        self.monitor.start()

        # Speed test thread (runs on demand)
        self.speed_test_thread: Optional[threading.Thread] = None
        
        # Start UI update timer (for chart refresh)
        self.after(1000, self._ui_update_loop)

    ############################################################################
    # Theme and styling
    ############################################################################
    def _apply_theme(self) -> None:
        """Apply theme and colours from the configuration."""
        theme = self.config.get("appearance", {}).get("theme", "light")
        accent = self.config.get("appearance", {}).get("accent_color", "#0066cc")
        font_size = self.config.get("appearance", {}).get("font_size", 10)
        # Basic theming: adjust background and foreground colours
        bg = "#ffffff" if theme == "light" else "#1e293b"
        fg = "#000000" if theme == "light" else "#f1f5f9"
        # Configure style options
        self.style.configure("TFrame", background=bg)
        self.style.configure("TNotebook", background=bg)
        self.style.configure("TNotebook.Tab", padding=6)
        self.style.configure("TLabel", background=bg, foreground=fg, font=("Segoe UI", font_size))
        self.style.configure("TButton", font=("Segoe UI", font_size))
        self.style.configure("Treeview", font=("Segoe UI", font_size-1))
        self.style.configure("Treeview.Heading", font=("Segoe UI", font_size, "bold"))
        # Badge styles (severity colours)
        # Tkinter's themed widgets require both a layout and configuration to be defined for
        # custom styles.  Without a layout, using a style on a ttk.Label will cause
        # ``TclError: Layout ... not found``.  To avoid this, copy the base ``TLabel``
        # layout for our custom badge styles.  Then configure the colours.
        base_layout = self.style.layout("TLabel")
        for sev, colour in self.issue_sev_colors.items():
            style_name = f"Badge.{sev}"
            # Copy the base TLabel layout to our custom style if not already defined
            try:
                # Check if layout exists; if not, an exception will be raised
                _ = self.style.layout(style_name)
            except Exception:
                self.style.layout(style_name, base_layout)
            # Configure background and foreground colours and font for the badge
            self.style.configure(style_name, background=colour, foreground="white", font=("Segoe UI", font_size, "bold"))
        # Accent colour for active elements
        self.style.configure("Accent.TButton", background=accent, foreground="white")

        # Card styles: use a simple relief and border to give panels a subtle raised
        # appearance reminiscent of modern dashboards.  These styles are applied to
        # frames and labelframes throughout the UI to group related widgets.  The
        # label frame style defines a bold font for its caption.
        self.style.configure("Card.TFrame", background=bg, relief="ridge", borderwidth=1)
        self.style.configure("Card.TLabelframe", background=bg, relief="ridge", borderwidth=1)
        self.style.configure("Card.TLabelframe.Label", background=bg, foreground=fg,
                             font=("Segoe UI", font_size, "bold"))

    ############################################################################
    # Dashboard Tab
    ############################################################################
    def _build_dashboard(self) -> None:
        """Construct the Dashboard tab UI using a grid layout for better responsiveness."""
        frame = self.tab_dashboard
        pad = {"padx": 10, "pady": 6}
        # Configure grid weights on the dashboard tab.  The top (badges) and control
        # rows should not expand when the window is resized; the chart row should
        # expand to fill available space when charts are enabled.
        # Set a single column to take up all horizontal space.
        frame.columnconfigure(0, weight=1)
        # Always have at least three rows: badges, controls, and last sample.  If
        # charts are enabled, row 2 (index 2) will expand; otherwise it remains
        # fixed.
        frame.rowconfigure(0, weight=0)
        frame.rowconfigure(1, weight=0)
        frame.rowconfigure(3, weight=0)
        # We'll configure the weight for row 2 dynamically below if charts are
        # shown.
        # Top row: badges showing current stats
        top = ttk.Frame(frame)
        # Place the badges row on the first grid row.  Use sticky EW so it
        # stretches horizontally when the window is resized.  Padding is
        # applied via the pad dict.
        top.grid(row=0, column=0, sticky="ew", **pad)
        # Labels and variables for badges
        self.var_ssid = tk.StringVar(value="—")
        self.var_state = tk.StringVar(value="disconnected")
        self.var_signal = tk.StringVar(value="0%")
        self.var_latency_gw = tk.StringVar(value="0 ms")
        self.var_latency_rem = tk.StringVar(value="0 ms")
        self.var_loss_gw = tk.StringVar(value="0%")
        self.var_loss_rem = tk.StringVar(value="0%")
        self.var_roams = tk.StringVar(value="0/h")
        self.var_throughput = tk.StringVar(value="0 Mbps")
        # Helper to create badge.  Each badge is a small frame containing a label
        # for the title and a value label styled according to severity.  The
        # outer frame is returned for placement within the badges row.
        def create_badge(parent: tk.Widget, label_text: str, var: tk.StringVar) -> ttk.Frame:
            outer = ttk.Frame(parent)
            lbl = ttk.Label(outer, text=label_text)
            lbl.pack(side=tk.TOP, anchor="w")
            val = ttk.Label(outer, textvariable=var, style="Badge.PASS")
            val.pack(fill=tk.X, pady=2)
            return outer
        # Add badges depending on dashboard layout config
        layout = self.config.get("dashboard_layout", {})
        badges = []
        badges.append(create_badge(top, "SSID", self.var_ssid))
        badges.append(create_badge(top, "State", self.var_state))
        if layout.get("show_signal", True):
            badges.append(create_badge(top, "Signal", self.var_signal))
        if layout.get("show_latency", True):
            badges.append(create_badge(top, "Latency (GW)", self.var_latency_gw))
            badges.append(create_badge(top, "Latency (Inet)", self.var_latency_rem))
            badges.append(create_badge(top, "Loss (GW)", self.var_loss_gw))
            badges.append(create_badge(top, "Loss (Inet)", self.var_loss_rem))
        if layout.get("show_roams", True):
            badges.append(create_badge(top, "Roams/hr", self.var_roams))
        if layout.get("show_throughput", True):
            badges.append(create_badge(top, "Throughput", self.var_throughput))
        # Arrange badges evenly using grid inside the top frame.  Each badge
        # occupies a separate column with equal weight so they distribute
        # evenly across the width.  Configure the column weights accordingly.
        for idx, badge in enumerate(badges):
            top.columnconfigure(idx, weight=1)
            badge.grid(row=0, column=idx, padx=6, sticky="ew")
        # Control buttons on dashboard.  Place them on the second grid row
        # (row=1).  Use sticky EW so the frame stretches across the width.
        ctrl_frame = ttk.Frame(frame)
        ctrl_frame.grid(row=1, column=0, sticky="ew", **pad)
        self.btn_start = ttk.Button(ctrl_frame, text="Start", command=self._start_monitor)
        self.btn_stop = ttk.Button(ctrl_frame, text="Stop", command=self._stop_monitor, state="disabled")
        self.btn_speed = ttk.Button(ctrl_frame, text="Run Speed Test", command=self._start_speed_test)
        self.btn_health = ttk.Button(ctrl_frame, text="Run Health Check", command=self.run_health_check)
        # Arrange buttons in the control frame using pack for simplicity.  The
        # control frame itself will expand horizontally with the grid.
        self.btn_start.pack(side=tk.LEFT, padx=4)
        self.btn_stop.pack(side=tk.LEFT, padx=4)
        self.btn_speed.pack(side=tk.LEFT, padx=4)
        self.btn_health.pack(side=tk.LEFT, padx=4)
        # Mini charts
        if layout.get("show_charts", True):
            # Charts occupy row 2.  Give this row a weight of 1 so it expands
            # to fill available vertical space when the window is resized.
            frame.rowconfigure(2, weight=1)
            chart_frame = ttk.LabelFrame(frame, text="Live Charts (10 minutes)")
            chart_frame.grid(row=2, column=0, sticky="nsew", padx=10, pady=6)
            # Create the figure with subplots for signal, gateway latency,
            # internet latency and download speed.  We avoid hardcoding
            # figure size here; instead, use a reasonable default and let
            # the containing frame's size dictate the canvas size.
            self.fig_dashboard = Figure(figsize=(6, 4), dpi=100)
            self.ax_signal = self.fig_dashboard.add_subplot(411)
            self.ax_signal.set_title("Signal %")
            self.ax_signal.set_ylim(0, 100)
            self.ax_signal.grid(True, alpha=0.3)
            self.ax_gw_lat = self.fig_dashboard.add_subplot(412)
            self.ax_gw_lat.set_title("Gateway Latency (ms)")
            self.ax_gw_lat.set_ylim(0, 300)
            self.ax_gw_lat.grid(True, alpha=0.3)
            self.ax_rem_lat = self.fig_dashboard.add_subplot(413)
            self.ax_rem_lat.set_title("Internet Latency (ms)")
            self.ax_rem_lat.set_ylim(0, 300)
            self.ax_rem_lat.grid(True, alpha=0.3)
            self.ax_throughput = self.fig_dashboard.add_subplot(414)
            self.ax_throughput.set_title("Download Speed (Mbps)")
            self.ax_throughput.set_ylim(0, 200)
            self.ax_throughput.grid(True, alpha=0.3)
            self.fig_dashboard.tight_layout()
            self.canvas_dashboard = FigureCanvasTkAgg(self.fig_dashboard, master=chart_frame)
            # Use grid and sticky N S E W for the canvas so it expands within
            # the chart_frame when the window is resized.
            canvas_widget = self.canvas_dashboard.get_tk_widget()
            canvas_widget.grid(row=0, column=0, sticky="nsew")
            chart_frame.rowconfigure(0, weight=1)
            chart_frame.columnconfigure(0, weight=1)
        # Last sample label
        self.var_last_sample = tk.StringVar(value="—")
        # Place last sample on its own row at the bottom of the dashboard (row=3)
        last_frame = ttk.Frame(frame)
        last_frame.grid(row=3, column=0, sticky="w", padx=(10, 10), pady=(4, 8))
        ttk.Label(last_frame, text="Last sample:").pack(side=tk.LEFT)
        ttk.Label(last_frame, textvariable=self.var_last_sample, style="Mono.TLabel").pack(side=tk.LEFT, padx=(4, 0))

    def _start_monitor(self) -> None:
        """Enable monitoring and update button states."""
        if not self.monitor.is_alive():
            # Recreate monitor thread with latest config if needed
            self.monitor = MonitorThread(self.config, self.db, self._on_monitor_summary)
            setattr(self.monitor, 'gui_run_health_check', self.run_health_check)
            self.monitor.start()
        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal")

    def _stop_monitor(self) -> None:
        """Stop monitoring thread and update button states."""
        self.monitor.stop()
        self.btn_start.configure(state="normal")
        self.btn_stop.configure(state="disabled")

    def _start_speed_test(self) -> None:
        """Run a throughput test in the background."""
        if not self.config.get("speed_test", {}).get("enabled", False):
            messagebox.showinfo("Speed Test", "Speed test is disabled in settings.")
            return
        if self.speed_test_thread and self.speed_test_thread.is_alive():
            messagebox.showinfo("Speed Test", "A speed test is already running.")
            return
        def run_test():
            st_cfg = self.config.get("speed_test", {})
            result = None
            if st_cfg.get("type", "http") == "iperf3" and iperf3 is not None:
                server = st_cfg.get("iperf3_server")
                port = int(st_cfg.get("iperf3_port", 5201))
                duration = int(st_cfg.get("duration", 10))
                result = iperf3_speed_test(server, port, duration) if server else None
            else:
                url = st_cfg.get("url")
                result = http_speed_test(url) if url else None
            self.monitor.last_speed_test = result
            # Update display on UI thread
            if result is not None:
                self.after(0, lambda: self.var_throughput.set(f"{result:.1f} Mbps"))
            else:
                self.after(0, lambda: self.var_throughput.set("Error"))
        self.speed_test_thread = threading.Thread(target=run_test, daemon=True)
        self.speed_test_thread.start()

    def _on_monitor_summary(self, summary: Dict) -> None:
        """Handle summary updates from the monitor thread on the UI thread."""
        # Use after() to run on main thread
        self.after(0, lambda: self._update_dashboard(summary))
        # Provide scan data to channels tab
        self.after(0, lambda: self._update_channels_tab(summary))

    def _update_dashboard(self, summary: Dict) -> None:
        """Update dashboard badges and charts with new summary data."""
        ts = summary.get("timestamp")
        intf = summary.get("interface", {})
        ping_gw = summary.get("ping_gateway", {})
        ping_rem = summary.get("ping_remote", {})
        throughput = summary.get("throughput")
        # Update badges
        self.var_ssid.set(intf.get("ssid") or "—")
        state = intf.get("state") or "disconnected"
        self.var_state.set(state)
        sig = intf.get("signal_pct") or "0%"
        self.var_signal.set(sig)
        # Determine badge severity based on thresholds
        thresholds = self.config.get("thresholds", {})
        def badge_style(value: float, warn: float, fail: float) -> str:
            try:
                v = float(value)
            except Exception:
                return "Badge.INFO"
            if v <= fail:
                return "Badge.FAIL"
            if v <= warn:
                return "Badge.WARN"
            return "Badge.PASS"
        # Signal
        try:
            sig_num = float(sig.replace("%", ""))
        except Exception:
            sig_num = float('nan')
        self.style.configure("Badge.Signal", background=self.issue_sev_colors.get(badge_style(sig_num, thresholds.get("signal_warn", 55), thresholds.get("signal_fail", 35)).split(".")[-1], "#3b82f6"))
        # Packet loss and latency badges
        gw_loss = ping_gw.get("loss")
        gw_lat = ping_gw.get("avg")
        rem_loss = ping_rem.get("loss")
        rem_lat = ping_rem.get("avg")
        # Format and update
        self.var_latency_gw.set(f"{gw_lat if gw_lat is not None else 0}")
        self.var_latency_rem.set(f"{rem_lat if rem_lat is not None else 0}")
        self.var_loss_gw.set(f"{gw_loss if gw_loss is not None else 0}%")
        self.var_loss_rem.set(f"{rem_loss if rem_loss is not None else 0}%")
        # Throughput
        if throughput is not None:
            self.var_throughput.set(f"{throughput:.1f} Mbps")
        # Roams/hr: compute number of roams in the last hour from file
        try:
            count = 0
            cutoff = datetime.now(timezone.utc) - timedelta(hours=1)
            with (Path(self.config["log_dir"]) / "roaming_events.csv").open("r", encoding="utf-8", errors="ignore") as f:
                next(f)  # skip header
                for line in f:
                    ts_str = line.split(",", 1)[0]
                    try:
                        ts_dt = datetime.fromisoformat(ts_str.replace("Z", "+00:00"))
                    except Exception:
                        continue
                    if ts_dt >= cutoff:
                        count += 1
            self.var_roams.set(f"{count}/h")
        except Exception:
            self.var_roams.set("0/h")
        # Last sample timestamp
        if ts:
            self.var_last_sample.set(ts.isoformat())
        # Update mini charts
        layout = self.config.get("dashboard_layout", {})
        if layout.get("show_charts", True):
            # Use buffer lists; create x axis as index
            xs = list(range(len(summary.get("signal_buffer", []))))
            # Clear axes
            self.ax_signal.clear(); self.ax_gw_lat.clear(); self.ax_rem_lat.clear(); self.ax_throughput.clear()
            # Plot signal
            sig_buf = summary.get("signal_buffer", [])
            self.ax_signal.plot(xs, sig_buf, color="#2563eb")
            self.ax_signal.set_title("Signal %")
            self.ax_signal.set_ylim(0, 100)
            self.ax_signal.grid(True, alpha=0.3)
            # Plot latency and throughput
            gw_buf = summary.get("ping_gw_buffer", [])
            rem_buf = summary.get("ping_rem_buffer", [])
            thr_buf = summary.get("throughput_buffer", [])
            self.ax_gw_lat.plot(xs, gw_buf, color="#047857")
            self.ax_gw_lat.set_title("Gateway Latency (ms)")
            self.ax_gw_lat.set_ylim(0, max(300, max([v for v in gw_buf if not math.isnan(v)], default=0) * 1.2))
            self.ax_gw_lat.grid(True, alpha=0.3)
            self.ax_rem_lat.plot(xs, rem_buf, color="#be185d")
            self.ax_rem_lat.set_title("Internet Latency (ms)")
            self.ax_rem_lat.set_ylim(0, max(300, max([v for v in rem_buf if not math.isnan(v)], default=0) * 1.2))
            self.ax_rem_lat.grid(True, alpha=0.3)
            self.ax_throughput.plot(xs, thr_buf, color="#92400e")
            self.ax_throughput.set_title("Download Speed (Mbps)")
            self.ax_throughput.set_ylim(0, max(200, max([v for v in thr_buf if not math.isnan(v)], default=0) * 1.2))
            self.ax_throughput.grid(True, alpha=0.3)
            self.fig_dashboard.tight_layout()
            self.canvas_dashboard.draw_idle()

    ############################################################################
    # Logs Tab
    ############################################################################
    def _build_logs_tab(self) -> None:
        """Construct the Logs tab UI."""
        frame = self.tab_logs
        # Filters
        filter_frame = ttk.Frame(frame)
        filter_frame.pack(fill=tk.X, padx=10, pady=6)
        ttk.Label(filter_frame, text="Search:").pack(side=tk.LEFT)
        self.var_log_search = tk.StringVar()
        self.entry_log_search = ttk.Entry(filter_frame, textvariable=self.var_log_search, width=30)
        self.entry_log_search.pack(side=tk.LEFT, padx=(4, 10))
        ttk.Label(filter_frame, text="Start (YYYY‑MM‑DD HH:MM):").pack(side=tk.LEFT)
        self.var_log_start = tk.StringVar()
        self.entry_log_start = ttk.Entry(filter_frame, textvariable=self.var_log_start, width=20)
        self.entry_log_start.pack(side=tk.LEFT, padx=4)
        ttk.Label(filter_frame, text="End (YYYY‑MM‑DD HH:MM):").pack(side=tk.LEFT)
        self.var_log_end = tk.StringVar()
        self.entry_log_end = ttk.Entry(filter_frame, textvariable=self.var_log_end, width=20)
        self.entry_log_end.pack(side=tk.LEFT, padx=4)
        ttk.Button(filter_frame, text="Apply Filter", command=self._apply_log_filter).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(filter_frame, text="Clear", command=self._clear_log_filter).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(filter_frame, text="Open CSV", command=self._open_csv).pack(side=tk.LEFT, padx=6)
        ttk.Button(filter_frame, text="Export", command=self._export_filtered_logs).pack(side=tk.LEFT, padx=6)
        # Treeview for CSV logs
        tree_frame = ttk.LabelFrame(frame, text="wifi_log.csv (filtered view)")
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 6))
        self.tree_logs = ttk.Treeview(tree_frame, columns=[], show="headings")
        self.tree_logs.pack(fill=tk.BOTH, expand=True)
        # JSON log view
        json_frame = ttk.LabelFrame(frame, text="wifi_log.jsonl (filtered view)")
        json_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 6))
        self.txt_json_logs = tk.Text(json_frame, height=10, wrap="none", font=("Cascadia Mono", 9))
        self.txt_json_logs.pack(fill=tk.BOTH, expand=True)
        # Initially load logs
        self._apply_log_filter()

    def _parse_log_time(self, s: str) -> Optional[datetime]:
        try:
            return datetime.fromisoformat(s)
        except Exception:
            try:
                return datetime.strptime(s, "%Y‑%m‑%d %H:%M")
            except Exception:
                return None

    def _apply_log_filter(self) -> None:
        """Filter log entries based on search term and date range."""
        csv_path = Path(self.config["log_dir"]) / "wifi_log.csv"
        jsonl_path = Path(self.config["log_dir"]) / "wifi_log.jsonl"
        search = self.var_log_search.get().lower().strip()
        start_ts = self._parse_log_time(self.var_log_start.get())
        end_ts = self._parse_log_time(self.var_log_end.get())
        # Load CSV
        rows = []
        header = []
        if csv_path.exists():
            with csv_path.open("r", encoding="utf-8", errors="ignore") as f:
                reader = csv.reader(f)
                header = next(reader, [])
                for row in reader:
                    ts_str = row[0]
                    try:
                        ts = datetime.fromisoformat(ts_str)
                    except Exception:
                        continue
                    if start_ts and ts < start_ts:
                        continue
                    if end_ts and ts > end_ts:
                        continue
                    if search and not any(search in cell.lower() for cell in row):
                        continue
                    rows.append(row)
        # Update treeview
        self.tree_logs.delete(*self.tree_logs.get_children())
        if header:
            self.tree_logs.configure(columns=header)
            for col in header:
                self.tree_logs.heading(col, text=col)
                self.tree_logs.column(col, width=100, minwidth=80, stretch=True)
            for row in rows[-500:]:  # show last 500 filtered entries
                self.tree_logs.insert("", "end", values=row)
        # Load JSONL and filter similarly
        self.txt_json_logs.delete("1.0", tk.END)
        if jsonl_path.exists():
            try:
                with jsonl_path.open("r", encoding="utf-8", errors="ignore") as jf:
                    lines = jf.readlines()
                # Filter last 200 lines
                lines = lines[-1000:]
                for ln in lines:
                    try:
                        entry = json.loads(ln)
                    except Exception:
                        continue
                    ts_str = entry.get("ts")
                    try:
                        ts_dt = datetime.fromisoformat(ts_str.replace("Z", "+00:00"))
                    except Exception:
                        continue
                    if start_ts and ts_dt < start_ts:
                        continue
                    if end_ts and ts_dt > end_ts:
                        continue
                    if search and search not in ln.lower():
                        continue
                    self.txt_json_logs.insert(tk.END, json.dumps(entry, indent=2) + "\n\n")
            except Exception:
                pass

    def _clear_log_filter(self) -> None:
        """Clear log filters and reload logs."""
        self.var_log_search.set("")
        self.var_log_start.set("")
        self.var_log_end.set("")
        self._apply_log_filter()

    def _open_csv(self) -> None:
        """Open the raw CSV log in the default editor (Windows only)."""
        path = Path(self.config["log_dir"]) / "wifi_log.csv"
        try:
            os.startfile(str(path))  # type: ignore
        except Exception:
            messagebox.showerror("Open CSV", "Could not open CSV file.")

    def _export_filtered_logs(self) -> None:
        """Export the filtered CSV and JSON logs to a file chosen by the user."""
        save_path = filedialog.asksaveasfilename(title="Export Logs", defaultextension=".zip",
                                                filetypes=[("ZIP Archives", "*.zip"), ("All Files", "*.*")])
        if not save_path:
            return
        try:
            with zipfile.ZipFile(save_path, "w", zipfile.ZIP_DEFLATED) as zf:
                # Write filtered CSV to memory
                csv_buf = io.StringIO()
                writer = csv.writer(csv_buf)
                # Write header
                columns = self.tree_logs["columns"]
                writer.writerow(columns)
                for item in self.tree_logs.get_children():
                    writer.writerow(self.tree_logs.item(item)["values"])
                zf.writestr("wifi_log_filtered.csv", csv_buf.getvalue())
                # Write filtered JSONL
                zf.writestr("wifi_log_filtered.jsonl", self.txt_json_logs.get("1.0", tk.END))
            messagebox.showinfo("Export", "Logs exported successfully.")
        except Exception as e:
            messagebox.showerror("Export", f"Failed to export logs: {e}")

    ############################################################################
    # Channels Tab
    ############################################################################
    def _build_channels_tab(self) -> None:
        """Construct the Channels tab UI."""
        frame = self.tab_channels
        # Top row: roam count and last roam
        top = ttk.Frame(frame)
        top.pack(fill=tk.X, padx=10, pady=6)
        self.var_roam_today = tk.StringVar(value="0")
        self.var_last_roam = tk.StringVar(value="—")
        ttk.Label(top, text="Roams today:").pack(side=tk.LEFT)
        ttk.Label(top, textvariable=self.var_roam_today, style="Big.TLabel").pack(side=tk.LEFT, padx=4)
        ttk.Label(top, text="Last roam:").pack(side=tk.LEFT, padx=(20, 0))
        ttk.Label(top, textvariable=self.var_last_roam, style="Big.TLabel").pack(side=tk.LEFT, padx=4)
        # Charts
        charts = ttk.Frame(frame)
        charts.pack(fill=tk.BOTH, expand=True, padx=10, pady=6)
        self.fig_channels = Figure(figsize=(7.0, 2.4), dpi=100)
        self.ax_24 = self.fig_channels.add_subplot(121)
        self.ax_5 = self.fig_channels.add_subplot(122)
        self.ax_24.set_title("2.4 GHz channels")
        self.ax_24.set_xlabel("Channel")
        self.ax_24.set_ylabel("Count")
        self.ax_5.set_title("5 GHz channels")
        self.ax_5.set_xlabel("Channel")
        self.ax_5.set_ylabel("Count")
        self.canvas_channels = FigureCanvasTkAgg(self.fig_channels, master=charts)
        self.canvas_channels.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        # Overlap warning
        warn_frame = ttk.Frame(frame)
        warn_frame.pack(fill=tk.X, padx=10, pady=(0, 6))
        ttk.Label(warn_frame, text="Overlap warning:").pack(side=tk.LEFT)
        self.var_overlap_warn = tk.StringVar(value="No obvious issues")
        ttk.Label(warn_frame, textvariable=self.var_overlap_warn, style="Warn.TLabel").pack(side=tk.LEFT, padx=4)
        # Top APs list
        top_ap_frame = ttk.LabelFrame(frame, text="Top 15 APs by signal (current scan)")
        top_ap_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        self.tree_top_aps = ttk.Treeview(top_ap_frame, columns=["ssid","bssid","channel","band","signal_pct"], show="headings")
        for col in ["ssid","bssid","channel","band","signal_pct"]:
            self.tree_top_aps.heading(col, text=col)
            self.tree_top_aps.column(col, width=130, stretch=True)
        self.tree_top_aps.pack(fill=tk.BOTH, expand=True)
        # Initially populate
        self._update_channels_tab({"scan_flat": []})

    def _update_channels_tab(self, summary: Dict) -> None:
        """Update channels tab based on the latest scan."""
        scan_flat = summary.get("scan_flat", [])
        # Roam counts (today)
        roam_path = Path(self.config["log_dir"]) / "roaming_events.csv"
        today = datetime.now(timezone.utc).date()
        roam_count = 0
        last_roam = "—"
        if roam_path.exists():
            try:
                with roam_path.open("r", encoding="utf-8", errors="ignore") as f:
                    next(f)
                    for line in f:
                        parts = line.strip().split(",")
                        if not parts:
                            continue
                        ts_str = parts[0]
                        try:
                            dt = datetime.fromisoformat(ts_str.replace("Z", "+00:00"))
                        except Exception:
                            continue
                        if dt.date() == today:
                            roam_count += 1
                        if not last_roam or dt > datetime.fromisoformat(last_roam.replace("Z", "+00:00")):
                            last_roam = ts_str
                self.var_roam_today.set(str(roam_count))
                self.var_last_roam.set(last_roam)
            except Exception:
                pass
        # Channel histogram
        ch24 = {}
        ch5 = {}
        for item in scan_flat:
            try:
                ch = int(item.get("channel", ""))
            except Exception:
                continue
            band = item.get("band")
            if band == "2.4":
                ch24[ch] = ch24.get(ch, 0) + 1
            elif band == "5":
                ch5[ch] = ch5.get(ch, 0) + 1
        # Update plots
        self.ax_24.clear(); self.ax_5.clear()
        if ch24:
            xs = sorted(ch24.keys()); ys = [ch24[x] for x in xs]
            colours = ["#c026d3" if x in (1, 6, 11) else "#c2410c" for x in xs]
            self.ax_24.bar(xs, ys, color=colours)
        self.ax_24.set_title("2.4 GHz channels")
        self.ax_24.set_xlabel("Channel"); self.ax_24.set_ylabel("Count")
        if ch5:
            xs5 = sorted(ch5.keys()); ys5 = [ch5[x] for x in xs5]
            self.ax_5.bar(xs5, ys5, color="#059669")
        self.ax_5.set_title("5 GHz channels")
        self.ax_5.set_xlabel("Channel"); self.ax_5.set_ylabel("Count")
        self.fig_channels.tight_layout()
        self.canvas_channels.draw_idle()
        # Overlap warning
        warn_msgs = []
        # Non‑1/6/11 channels
        bad = [str(c) for c in ch24.keys() if c not in (1, 6, 11)]
        if bad:
            warn_msgs.append("Non‑1/6/11 channels present: " + ", ".join(bad))
        # Crowded channels: if sum counts across ±2 channels >=8
        for c in ch24.keys():
            crowd = sum(ch24.get(cc, 0) for cc in range(c-2, c+3))
            if crowd >= 8:
                warn_msgs.append(f"Crowded around ch {c} (≈{crowd} BSSIDs)")
                break
        self.var_overlap_warn.set("; ".join(warn_msgs) if warn_msgs else "No obvious issues")
        # Top APs list
        self.tree_top_aps.delete(*self.tree_top_aps.get_children())
        for row in scan_flat[:15]:
            self.tree_top_aps.insert("", "end", values=[row["ssid"], row["bssid"], row["channel"], row["band"], row["signal_pct"]])

    ############################################################################
    # Diagnostics Tab
    ############################################################################
    def _build_diagnostics_tab(self) -> None:
        """Construct the Diagnostics tab UI."""
        frame = self.tab_diag
        # Filter controls for category and severity
        filter_frame = ttk.Frame(frame)
        filter_frame.pack(fill=tk.X, padx=10, pady=6)
        ttk.Label(filter_frame, text="Category:").pack(side=tk.LEFT)
        categories = ["All"] + sorted(set(entry.get("category", "") for entry in self.db.values()))
        cmb_cat = ttk.Combobox(filter_frame, values=categories, textvariable=self.diag_filter_category, state="readonly", width=20)
        cmb_cat.pack(side=tk.LEFT, padx=(4, 10))
        cmb_cat.bind("<<ComboboxSelected>>", lambda _: self._populate_diagnostics_ui())
        ttk.Label(filter_frame, text="Severity:").pack(side=tk.LEFT)
        cmb_sev = ttk.Combobox(filter_frame, values=["All", "FAIL", "WARN", "INFO", "PASS"], textvariable=self.diag_filter_severity, state="readonly", width=12)
        cmb_sev.pack(side=tk.LEFT, padx=(4, 10))
        cmb_sev.bind("<<ComboboxSelected>>", lambda _: self._populate_diagnostics_ui())
        ttk.Button(filter_frame, text="Refresh", command=self.run_health_check).pack(side=tk.LEFT)
        ttk.Button(filter_frame, text="Export Report", command=self.generate_report).pack(side=tk.LEFT, padx=6)
        # Issues list
        issues_frame = ttk.LabelFrame(frame, text="Detected Issues")
        issues_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 6))
        self.tree_issues = ttk.Treeview(issues_frame, columns=["sev", "issue"], show="headings", height=10)
        self.tree_issues.heading("sev", text="Severity")
        self.tree_issues.heading("issue", text="Issue")
        self.tree_issues.column("sev", width=80, anchor="center")
        self.tree_issues.column("issue", width=300, anchor="w")
        self.tree_issues.pack(fill=tk.BOTH, expand=True)
        self.tree_issues.bind("<<TreeviewSelect>>", self._on_issue_select)
        # Details panel
        details_frame = ttk.LabelFrame(frame, text="Details")
        details_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        # Text details
        self.text_issue_detail = tk.Text(details_frame, height=8, wrap="word", font=("Segoe UI", 9))
        self.text_issue_detail.pack(fill=tk.BOTH, expand=True, padx=6, pady=4)
        # Chart for issue details (optional)
        self.fig_issue = Figure(figsize=(5.0, 2.2), dpi=100)
        self.ax_issue = self.fig_issue.add_subplot(111)
        self.canvas_issue = FigureCanvasTkAgg(self.fig_issue, master=details_frame)
        self.canvas_issue.get_tk_widget().pack(fill=tk.BOTH, expand=False, padx=6, pady=(0, 6))

    def run_health_check(self) -> None:
        """Run diagnostics and populate the issues list and details panel."""
        # Run diagnostics in a background thread to keep UI responsive
        def worker():
            issues: List[Tuple[str, str]] = []  # (severity, issue_id)
            # Service & adapter checks
            # Check WLAN service state
            svc = run_command('sc query wlansvc', timeout=5)
            if 'RUNNING' not in svc:
                issues.append(("FAIL", "wlan_service_not_running"))
            # Adapter disconnected
            if self.var_state.get().lower() == 'disconnected' or self.var_ssid.get() == "—":
                issues.append(("FAIL", "adapter_disconnected"))
            # Signal thresholds
            try:
                sig = float(self.var_signal.get().replace('%', ''))
            except Exception:
                sig = float('nan')
            if not math.isnan(sig):
                thr = self.config.get("thresholds", {})
                if sig < thr.get("signal_fail", 35):
                    issues.append(("FAIL", "weak_signal"))
                elif sig < thr.get("signal_warn", 55):
                    issues.append(("WARN", "moderate_signal"))
            # Packet loss and latency thresholds
            try:
                gw_loss = int(self.var_loss_gw.get().replace('%', ''))
            except Exception:
                gw_loss = None
            try:
                rem_loss = int(self.var_loss_rem.get().replace('%', ''))
            except Exception:
                rem_loss = None
            try:
                gw_lat = float(self.var_latency_gw.get())
            except Exception:
                gw_lat = None
            try:
                rem_lat = float(self.var_latency_rem.get())
            except Exception:
                rem_lat = None
            thr = self.config.get("thresholds", {})
            if gw_loss is not None:
                if gw_loss > thr.get("loss_fail", 20):
                    issues.append(("FAIL", "gateway_packet_loss"))
                elif gw_loss > thr.get("loss_warn", 10):
                    issues.append(("WARN", "gateway_packet_loss"))
            if rem_loss is not None:
                if rem_loss > thr.get("loss_fail", 20):
                    issues.append(("FAIL", "internet_packet_loss"))
                elif rem_loss > thr.get("loss_warn", 10):
                    issues.append(("WARN", "internet_packet_loss"))
            if gw_lat is not None:
                if gw_lat > thr.get("latency_fail", 300):
                    issues.append(("FAIL", "gateway_high_latency"))
                elif gw_lat > thr.get("latency_warn", 150):
                    issues.append(("WARN", "gateway_high_latency"))
            if rem_lat is not None:
                if rem_lat > thr.get("latency_fail", 300):
                    issues.append(("FAIL", "internet_high_latency"))
                elif rem_lat > thr.get("latency_warn", 150):
                    issues.append(("WARN", "internet_high_latency"))
            # Roaming frequency (per hour)
            roam_count = 0
            now = datetime.now(timezone.utc)
            try:
                with (Path(self.config["log_dir"]) / "roaming_events.csv").open("r", encoding="utf-8", errors="ignore") as f:
                    next(f)
                    for line in f:
                        ts_str = line.split(',', 1)[0]
                        dt = datetime.fromisoformat(ts_str.replace("Z", "+00:00"))
                        if (now - dt).total_seconds() <= 3600:
                            roam_count += 1
            except Exception:
                pass
            if roam_count >= 6:
                issues.append(("FAIL", "excessive_roaming"))
            elif roam_count >= 3:
                issues.append(("WARN", "moderate_roaming"))
            # Channel plan and crowding
            # Evaluate based on current channels data
            # We already computed this in channels tab; reuse that info if possible
            # Check for bad channels
            summary = {
                "scan_flat": getattr(self.monitor, "_flatten_scan", lambda x: [])(parse_netsh_scan(run_command("netsh wlan show networks mode=bssid")))
            }
            ch24 = {}
            for item in summary["scan_flat"]:
                if item.get("band") == "2.4":
                    try:
                        c = int(item.get("channel"))
                        ch24[c] = ch24.get(c, 0) + 1
                    except Exception:
                        continue
            if any(c not in (1, 6, 11) for c in ch24):
                issues.append(("WARN", "bad_channel_plan"))
            # Crowding
            for c in ch24:
                crowd = sum(ch24.get(cc, 0) for cc in range(c-2, c+3))
                if crowd >= 8:
                    issues.append(("WARN", "crowded_channel"))
                    break
            # Power management and driver issues (heuristics based on logs)
            # Analyse historical logs for frequent disconnects, low signal etc.
            log_issues = self._analyse_logs()
            issues.extend(log_issues)
            # Remove duplicates and keep worst severity
            unique: Dict[str, str] = {}
            for sev, iid in issues:
                if iid not in unique:
                    unique[iid] = sev
                else:
                    # Preserve worst severity (FAIL > WARN > INFO > PASS)
                    order = {"PASS": 0, "INFO": 1, "WARN": 2, "FAIL": 3}
                    if order[sev] > order[unique[iid]]:
                        unique[iid] = sev
            # Populate UI on main thread
            def update_ui():
                self.current_issues = [(unique[iid], iid) for iid in unique]
                self._populate_diagnostics_ui()
                # Show summary pop‑up
                fails = sum(1 for sev in unique.values() if sev == "FAIL")
                warns = sum(1 for sev in unique.values() if sev == "WARN")
                if fails or warns:
                    msg = []
                    if fails:
                        msg.append(f"{fails} failure(s)")
                    if warns:
                        msg.append(f"{warns} warning(s)")
                    messagebox.showwarning("Diagnostics", "\n".join(msg))
                else:
                    messagebox.showinfo("Diagnostics", "No major issues detected.")
            self.after(0, update_ui)
        threading.Thread(target=worker, daemon=True).start()

    def _analyse_logs(self) -> List[Tuple[str, str]]:
        """Analyse recent logs to detect patterns like frequent disconnects or low average signal."""
        issues: List[Tuple[str, str]] = []
        log_path = Path(self.config["log_dir"]) / "wifi_log.csv"
        if not log_path.exists():
            return issues
        try:
            # Read last 1000 entries
            rows = []
            with log_path.open("r", encoding="utf-8", errors="ignore") as f:
                reader = csv.reader(f)
                header = next(reader, [])
                for row in reader:
                    rows.append(row)
            rows = rows[-1000:]
            # Indices of fields
            idx_state = header.index("state") if "state" in header else 1
            idx_signal = header.index("signal_pct") if "signal_pct" in header else 4
            idx_ping_gw_loss = header.index("ping_gateway_loss") if "ping_gateway_loss" in header else 8
            idx_ping_rem_loss = header.index("ping_remote_loss") if "ping_remote_loss" in header else 10
            # Compute metrics
            disc = 0
            sig_vals = []
            gw_loss_high = 0
            rem_loss_high = 0
            for row in rows:
                if idx_state < len(row) and row[idx_state].lower() == 'disconnected':
                    disc += 1
                if idx_signal < len(row):
                    try:
                        s = float(row[idx_signal].replace('%',''))
                        sig_vals.append(s)
                    except Exception:
                        pass
                if idx_ping_gw_loss < len(row):
                    try:
                        l = int(row[idx_ping_gw_loss])
                        if l > self.config.get("thresholds", {}).get("loss_warn", 10):
                            gw_loss_high += 1
                    except Exception:
                        pass
                if idx_ping_rem_loss < len(row):
                    try:
                        l2 = int(row[idx_ping_rem_loss])
                        if l2 > self.config.get("thresholds", {}).get("loss_warn", 10):
                            rem_loss_high += 1
                    except Exception:
                        pass
            # Frequent disconnections
            if disc > 5:
                issues.append(("WARN", "frequent_disconnections"))
            # Average signal
            if sig_vals:
                avg_sig = sum(sig_vals) / len(sig_vals)
                if avg_sig < self.config.get("thresholds", {}).get("signal_fail", 35):
                    issues.append(("WARN", "low_average_signal_log"))
                elif avg_sig < self.config.get("thresholds", {}).get("signal_warn", 55):
                    issues.append(("INFO", "moderate_average_signal_log"))
            # Many roam events from historical log
            roam_log = Path(self.config["log_dir"]) / "roaming_events.csv"
            if roam_log.exists():
                try:
                    with roam_log.open("r", encoding="utf-8", errors="ignore") as f:
                        next(f)
                        lines = f.readlines()
                    if len(lines) > 20:
                        issues.append(("INFO", "many_roam_events"))
                except Exception:
                    pass
            return issues
        except Exception:
            return issues

    def _populate_diagnostics_ui(self) -> None:
        """Refresh the diagnostics list based on current_issues and filters."""
        self.tree_issues.delete(*self.tree_issues.get_children())
        cat_filter = self.diag_filter_category.get()
        sev_filter = self.diag_filter_severity.get()
        for sev, iid in self.current_issues:
            entry = self.db.get(iid, {})
            category = entry.get("category", "")
            if (cat_filter != "All" and category != cat_filter):
                continue
            if (sev_filter != "All" and sev != sev_filter):
                continue
            self.tree_issues.insert("", "end", values=(sev, entry.get("title", iid)), tags=(sev, iid))
        # Apply tag styles
        for sev in ["FAIL", "WARN", "INFO", "PASS"]:
            colour = self.issue_sev_colors.get(sev)
            if colour:
                self.tree_issues.tag_configure(sev, background=colour, foreground="white")
        # Clear details
        self.text_issue_detail.delete("1.0", tk.END)
        self.ax_issue.clear(); self.canvas_issue.draw_idle()

    def _on_issue_select(self, event) -> None:
        """Display details for the selected issue."""
        sel = self.tree_issues.selection()
        if not sel:
            return
        item = self.tree_issues.item(sel[0])
        values = item.get("values")
        if not values:
            return
        sev, title = values[0], values[1]
        # Find issue id by title
        issue_id = None
        for iid, entry in self.db.items():
            if entry.get("title") == title:
                issue_id = iid
                break
        if not issue_id:
            self.text_issue_detail.delete("1.0", tk.END)
            self.text_issue_detail.insert(tk.END, "Unknown issue.")
            return
        entry = self.db.get(issue_id, {})
        # Display description, causes, resolutions
        self.text_issue_detail.delete("1.0", tk.END)
        self.text_issue_detail.insert(tk.END, f"{entry.get('title')}\n\n")
        self.text_issue_detail.insert(tk.END, f"{entry.get('description')}\n\n")
        if entry.get("causes"):
            self.text_issue_detail.insert(tk.END, "Possible Causes:\n", ("bold",))
            for c in entry["causes"]:
                self.text_issue_detail.insert(tk.END, f" • {c}\n")
            self.text_issue_detail.insert(tk.END, "\n")
        if entry.get("resolutions"):
            self.text_issue_detail.insert(tk.END, "Recommended Fixes:\n", ("bold",))
            for r in entry["resolutions"]:
                self.text_issue_detail.insert(tk.END, f" • {r}\n")
            self.text_issue_detail.insert(tk.END, "\n")
        if entry.get("links"):
            self.text_issue_detail.insert(tk.END, "Links:\n", ("bold",))
            for label, cmd in entry["links"]:
                self.text_issue_detail.insert(tk.END, f" • {label} ({cmd})\n")
        # Bold style for headings
        self.text_issue_detail.tag_configure("bold", font=("Segoe UI", 9, "bold"))
        # Draw graph for this issue (if applicable)
        self.ax_issue.clear()
        fig_needed = False
        if issue_id in ("weak_signal", "low_average_signal_log", "moderate_signal", "moderate_average_signal_log"):
            # Plot signal history
            xs = list(range(len(self.monitor.buf_signal)))
            self.ax_issue.plot(xs, list(self.monitor.buf_signal), color="#2563eb")
            self.ax_issue.set_title("Signal History (%)")
            self.ax_issue.set_ylim(0, 100)
            fig_needed = True
        elif issue_id in ("gateway_packet_loss", "internet_packet_loss"):
            # Plot packet loss occurrences (bar)
            gw_losses = [l for l in self.monitor.buf_ping_gw if not math.isnan(l)]
            rem_losses = [l for l in self.monitor.buf_ping_rem if not math.isnan(l)]
            if issue_id == "gateway_packet_loss" and gw_losses:
                self.ax_issue.plot(list(range(len(gw_losses))), gw_losses, color="#f59e0b")
                self.ax_issue.set_title("Gateway Latency History (ms)")
                fig_needed = True
            if issue_id == "internet_packet_loss" and rem_losses:
                self.ax_issue.plot(list(range(len(rem_losses))), rem_losses, color="#be185d")
                self.ax_issue.set_title("Internet Latency History (ms)")
                fig_needed = True
        elif issue_id in ("gateway_high_latency", "internet_high_latency"):
            # Plot latency history
            buf = self.monitor.buf_ping_gw if issue_id == "gateway_high_latency" else self.monitor.buf_ping_rem
            self.ax_issue.plot(list(range(len(buf))), list(buf), color="#ea580c")
            self.ax_issue.set_title("Latency History (ms)")
            fig_needed = True
        elif issue_id in ("bad_channel_plan", "crowded_channel"):
            # Plot channel histogram from last scan
            scan_flat = getattr(self.monitor, "_flatten_scan", lambda x: [])(parse_netsh_scan(run_command("netsh wlan show networks mode=bssid")))
            ch24 = {}
            for item in scan_flat:
                if item.get("band") == "2.4":
                    try:
                        c = int(item.get("channel", ""))
                        ch24[c] = ch24.get(c, 0) + 1
                    except Exception:
                        continue
            self.ax_issue.bar(ch24.keys(), ch24.values(), color="#facc15")
            self.ax_issue.set_title("2.4 GHz Channel Histogram")
            fig_needed = True
        if fig_needed:
            self.fig_issue.tight_layout()
            self.canvas_issue.draw_idle()
        else:
            self.canvas_issue.get_tk_widget().pack_forget()
            self.canvas_issue.get_tk_widget().pack(fill=tk.BOTH, expand=False, padx=6, pady=(0, 6))

    ############################################################################
    # Settings Tab
    ############################################################################
    def _build_settings_tab(self) -> None:
        """Construct the Settings tab UI."""
        frame = self.tab_settings
        pad = {"padx": 10, "pady": 6}
        # Use Notebook inside settings to organise sections
        nb = ttk.Notebook(frame)
        nb.pack(fill=tk.BOTH, expand=True)
        # Appearance section
        sec_app = ttk.Frame(nb)
        nb.add(sec_app, text="Appearance")
        ttk.Label(sec_app, text="Theme:").grid(row=0, column=0, sticky="w", **pad)
        theme_var = tk.StringVar(value=self.config.get("appearance", {}).get("theme", "light"))
        ttk.Combobox(sec_app, values=["light", "dark"], textvariable=theme_var, state="readonly")\
            .grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(sec_app, text="Accent colour:").grid(row=1, column=0, sticky="w", **pad)
        accent_var = tk.StringVar(value=self.config.get("appearance", {}).get("accent_color", "#0066cc"))
        ttk.Entry(sec_app, textvariable=accent_var).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_app, text="Font size:").grid(row=2, column=0, sticky="w", **pad)
        font_var = tk.IntVar(value=self.config.get("appearance", {}).get("font_size", 10))
        ttk.Spinbox(sec_app, from_=8, to=16, textvariable=font_var, width=5).grid(row=2, column=1, sticky="w", **pad)
        # Dashboard layout section
        sec_dash = ttk.Frame(nb)
        nb.add(sec_dash, text="Dashboard")
        dl = self.config.get("dashboard_layout", {})
        self.var_show_signal = tk.BooleanVar(value=dl.get("show_signal", True))
        self.var_show_latency = tk.BooleanVar(value=dl.get("show_latency", True))
        self.var_show_roams = tk.BooleanVar(value=dl.get("show_roams", True))
        self.var_show_throughput = tk.BooleanVar(value=dl.get("show_throughput", True))
        self.var_show_charts = tk.BooleanVar(value=dl.get("show_charts", True))
        ttk.Checkbutton(sec_dash, text="Show signal badge", variable=self.var_show_signal).grid(row=0, column=0, sticky="w", **pad)
        ttk.Checkbutton(sec_dash, text="Show latency & loss badges", variable=self.var_show_latency).grid(row=1, column=0, sticky="w", **pad)
        ttk.Checkbutton(sec_dash, text="Show roaming badge", variable=self.var_show_roams).grid(row=2, column=0, sticky="w", **pad)
        ttk.Checkbutton(sec_dash, text="Show throughput badge", variable=self.var_show_throughput).grid(row=3, column=0, sticky="w", **pad)
        ttk.Checkbutton(sec_dash, text="Show live charts", variable=self.var_show_charts).grid(row=4, column=0, sticky="w", **pad)
        # Thresholds section
        sec_thr = ttk.Frame(nb)
        nb.add(sec_thr, text="Thresholds")
        thr = self.config.get("thresholds", {})
        ttk.Label(sec_thr, text="Signal warn (%):").grid(row=0, column=0, sticky="w", **pad)
        sig_warn_var = tk.IntVar(value=thr.get("signal_warn", 55))
        ttk.Spinbox(sec_thr, from_=10, to=90, textvariable=sig_warn_var, width=5).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(sec_thr, text="Signal fail (%):").grid(row=1, column=0, sticky="w", **pad)
        sig_fail_var = tk.IntVar(value=thr.get("signal_fail", 35))
        ttk.Spinbox(sec_thr, from_=5, to=80, textvariable=sig_fail_var, width=5).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_thr, text="Loss warn (%):").grid(row=2, column=0, sticky="w", **pad)
        loss_warn_var = tk.IntVar(value=thr.get("loss_warn", 10))
        ttk.Spinbox(sec_thr, from_=0, to=100, textvariable=loss_warn_var, width=5).grid(row=2, column=1, sticky="w", **pad)
        ttk.Label(sec_thr, text="Loss fail (%):").grid(row=3, column=0, sticky="w", **pad)
        loss_fail_var = tk.IntVar(value=thr.get("loss_fail", 20))
        ttk.Spinbox(sec_thr, from_=0, to=100, textvariable=loss_fail_var, width=5).grid(row=3, column=1, sticky="w", **pad)
        ttk.Label(sec_thr, text="Latency warn (ms):").grid(row=4, column=0, sticky="w", **pad)
        lat_warn_var = tk.IntVar(value=thr.get("latency_warn", 150))
        ttk.Spinbox(sec_thr, from_=10, to=1000, textvariable=lat_warn_var, width=6).grid(row=4, column=1, sticky="w", **pad)
        ttk.Label(sec_thr, text="Latency fail (ms):").grid(row=5, column=0, sticky="w", **pad)
        lat_fail_var = tk.IntVar(value=thr.get("latency_fail", 300))
        ttk.Spinbox(sec_thr, from_=50, to=2000, textvariable=lat_fail_var, width=6).grid(row=5, column=1, sticky="w", **pad)
        # Monitoring settings
        sec_mon = ttk.Frame(nb)
        nb.add(sec_mon, text="Monitoring")
        ttk.Label(sec_mon, text="Scan interval (s):").grid(row=0, column=0, sticky="w", **pad)
        scan_var = tk.IntVar(value=self.config.get("scan_interval", 10))
        ttk.Spinbox(sec_mon, from_=2, to=60, textvariable=scan_var, width=6).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(sec_mon, text="Ping count:").grid(row=1, column=0, sticky="w", **pad)
        ping_var = tk.IntVar(value=self.config.get("ping_count", 4))
        ttk.Spinbox(sec_mon, from_=1, to=10, textvariable=ping_var, width=4).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_mon, text="Gateway IP:").grid(row=2, column=0, sticky="w", **pad)
        gw_var = tk.StringVar(value=self.config.get("ping_targets", {}).get("gateway") or "")
        ttk.Entry(sec_mon, textvariable=gw_var).grid(row=2, column=1, sticky="w", **pad)
        ttk.Label(sec_mon, text="Remote host:").grid(row=3, column=0, sticky="w", **pad)
        rem_var = tk.StringVar(value=self.config.get("ping_targets", {}).get("remote", "8.8.8.8"))
        ttk.Entry(sec_mon, textvariable=rem_var).grid(row=3, column=1, sticky="w", **pad)
        # Log settings
        sec_log = ttk.Frame(nb)
        nb.add(sec_log, text="Logging")
        ttk.Label(sec_log, text="Log directory:").grid(row=0, column=0, sticky="w", **pad)
        logdir_var = tk.StringVar(value=self.config.get("log_dir", "logs"))
        ttk.Entry(sec_log, textvariable=logdir_var, width=40).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(sec_log, text="Retention days:").grid(row=1, column=0, sticky="w", **pad)
        retain_var = tk.IntVar(value=self.config.get("log_retention_days", 14))
        ttk.Spinbox(sec_log, from_=1, to=90, textvariable=retain_var, width=5).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_log, text="Max log size (MB):").grid(row=2, column=0, sticky="w", **pad)
        max_mb_var = tk.IntVar(value=self.config.get("max_log_mb", 512))
        ttk.Spinbox(sec_log, from_=10, to=2048, textvariable=max_mb_var, width=6).grid(row=2, column=1, sticky="w", **pad)
        # Notifications settings
        sec_not = ttk.Frame(nb)
        nb.add(sec_not, text="Notifications")
        ncfg = self.config.get("notifications", {})
        notif_enabled_var = tk.BooleanVar(value=ncfg.get("enabled", True))
        ttk.Checkbutton(sec_not, text="Enable notifications", variable=notif_enabled_var).grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(sec_not, text="Signal threshold (%):").grid(row=1, column=0, sticky="w", **pad)
        notif_sig_var = tk.IntVar(value=ncfg.get("signal_threshold", 35))
        ttk.Spinbox(sec_not, from_=5, to=90, textvariable=notif_sig_var, width=5).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_not, text="Loss threshold (%):").grid(row=2, column=0, sticky="w", **pad)
        notif_loss_var = tk.IntVar(value=ncfg.get("loss_threshold", 20))
        ttk.Spinbox(sec_not, from_=0, to=100, textvariable=notif_loss_var, width=5).grid(row=2, column=1, sticky="w", **pad)
        ttk.Label(sec_not, text="Latency threshold (ms):").grid(row=3, column=0, sticky="w", **pad)
        notif_lat_var = tk.IntVar(value=ncfg.get("latency_threshold", 200))
        ttk.Spinbox(sec_not, from_=50, to=2000, textvariable=notif_lat_var, width=6).grid(row=3, column=1, sticky="w", **pad)
        ttk.Label(sec_not, text="Channels:").grid(row=4, column=0, sticky="w", **pad)
        notif_channels_var = tk.StringVar(value=",".join(ncfg.get("channels", ["popup"])))
        ttk.Entry(sec_not, textvariable=notif_channels_var).grid(row=4, column=1, sticky="w", **pad)
        # Speed test settings
        sec_speed = ttk.Frame(nb)
        nb.add(sec_speed, text="Speed Test")
        st = self.config.get("speed_test", {})
        speed_enabled_var = tk.BooleanVar(value=st.get("enabled", False))
        ttk.Checkbutton(sec_speed, text="Enable speed test", variable=speed_enabled_var).grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(sec_speed, text="Test type:").grid(row=1, column=0, sticky="w", **pad)
        speed_type_var = tk.StringVar(value=st.get("type", "http"))
        ttk.Combobox(sec_speed, values=["http", "iperf3"], textvariable=speed_type_var, state="readonly")\
            .grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(sec_speed, text="HTTP URL:").grid(row=2, column=0, sticky="w", **pad)
        speed_url_var = tk.StringVar(value=st.get("url", "http://speedtest.tele2.net/1MB.zip"))
        ttk.Entry(sec_speed, textvariable=speed_url_var, width=40).grid(row=2, column=1, sticky="w", **pad)
        ttk.Label(sec_speed, text="iPerf3 server:").grid(row=3, column=0, sticky="w", **pad)
        speed_server_var = tk.StringVar(value=st.get("iperf3_server", ""))
        ttk.Entry(sec_speed, textvariable=speed_server_var).grid(row=3, column=1, sticky="w", **pad)
        ttk.Label(sec_speed, text="iPerf3 port:").grid(row=4, column=0, sticky="w", **pad)
        speed_port_var = tk.IntVar(value=st.get("iperf3_port", 5201))
        ttk.Spinbox(sec_speed, from_=1, to=65535, textvariable=speed_port_var, width=6).grid(row=4, column=1, sticky="w", **pad)
        ttk.Label(sec_speed, text="Duration (s):").grid(row=5, column=0, sticky="w", **pad)
        speed_dur_var = tk.IntVar(value=st.get("duration", 10))
        ttk.Spinbox(sec_speed, from_=5, to=60, textvariable=speed_dur_var, width=4).grid(row=5, column=1, sticky="w", **pad)
        # Scheduled diagnostics settings
        sec_sched = ttk.Frame(nb)
        nb.add(sec_sched, text="Scheduled Diagnostics")
        sched = self.config.get("scheduled_diagnostics", {})
        sched_enabled_var = tk.BooleanVar(value=sched.get("enabled", False))
        ttk.Checkbutton(sec_sched, text="Enable scheduled diagnostics", variable=sched_enabled_var).grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(sec_sched, text="Interval (hours):").grid(row=1, column=0, sticky="w", **pad)
        sched_interval_var = tk.IntVar(value=sched.get("interval_hours", 12))
        ttk.Spinbox(sec_sched, from_=1, to=24*7, textvariable=sched_interval_var, width=5).grid(row=1, column=1, sticky="w", **pad)
        # Save button
        def save_settings():
            # Update config dict
            self.config["appearance"] = {
                "theme": theme_var.get(),
                "accent_color": accent_var.get(),
                "font_size": font_var.get(),
            }
            self.config["dashboard_layout"] = {
                "show_signal": self.var_show_signal.get(),
                "show_latency": self.var_show_latency.get(),
                "show_roams": self.var_show_roams.get(),
                "show_throughput": self.var_show_throughput.get(),
                "show_charts": self.var_show_charts.get(),
            }
            self.config["thresholds"] = {
                "signal_warn": sig_warn_var.get(),
                "signal_fail": sig_fail_var.get(),
                "loss_warn": loss_warn_var.get(),
                "loss_fail": loss_fail_var.get(),
                "latency_warn": lat_warn_var.get(),
                "latency_fail": lat_fail_var.get(),
            }
            self.config["scan_interval"] = scan_var.get()
            self.config["ping_count"] = ping_var.get()
            self.config["ping_targets"] = {
                "gateway": gw_var.get() or None,
                "remote": rem_var.get() or None,
            }
            self.config["log_dir"] = logdir_var.get()
            self.config["log_retention_days"] = retain_var.get()
            self.config["max_log_mb"] = max_mb_var.get()
            self.config["notifications"] = {
                "enabled": notif_enabled_var.get(),
                "signal_threshold": notif_sig_var.get(),
                "loss_threshold": notif_loss_var.get(),
                "latency_threshold": notif_lat_var.get(),
                "channels": [c.strip() for c in notif_channels_var.get().split(',') if c.strip()],
            }
            self.config["speed_test"] = {
                "enabled": speed_enabled_var.get(),
                "type": speed_type_var.get(),
                "url": speed_url_var.get(),
                "iperf3_server": speed_server_var.get(),
                "iperf3_port": speed_port_var.get(),
                "duration": speed_dur_var.get(),
            }
            self.config["scheduled_diagnostics"] = {
                "enabled": sched_enabled_var.get(),
                "interval_hours": sched_interval_var.get(),
            }
            # Save to YAML
            save_config(self.config)
            # Reapply theme and refresh UI
            self._apply_theme()
            # Possibly restart monitor thread with new settings
            self._stop_monitor()
            self._start_monitor()
            messagebox.showinfo("Settings", "Settings saved. Some changes may require restarting the application.")
        ttk.Button(frame, text="Save Settings", command=save_settings).pack(pady=(4, 10))

    ############################################################################
    # Report Generation
    ############################################################################
    def generate_report(self) -> None:
        """Generate a simple HTML report summarising recent diagnostics and logs."""
        save_path = filedialog.asksaveasfilename(title="Save Report", defaultextension=".html",
                                                filetypes=[("HTML Files", "*.html")])
        if not save_path:
            return
        try:
            # Compose HTML
            html = ["<html><head><meta charset='utf-8'><title>Wi‑Fi Report</title>\n" +
                    "<style>body{font-family:sans-serif;margin:20px;}h1,h2{color:#0f172a;}"
                    "table{border-collapse:collapse;width:100%;}th,td{border:1px solid #ccc;padding:4px;text-align:left;}"
                    "th{background-color:#f8fafc;}" +
                    "</style></head><body>"]
            html.append("<h1>Wi‑Fi Diagnostics Report</h1>")
            html.append(f"<p>Generated: {datetime.now(timezone.utc).isoformat()}</p>")
            # Summary of signal and latency over last 10 minutes
            html.append("<h2>Recent Signal & Latency</h2>")
            # Generate charts as PNG and embed base64
            buf = io.BytesIO()
            fig = Figure(figsize=(6, 4), dpi=100)
            ax1 = fig.add_subplot(311)
            ax2 = fig.add_subplot(312)
            ax3 = fig.add_subplot(313)
            xs = list(range(len(self.monitor.buf_signal)))
            ax1.plot(xs, list(self.monitor.buf_signal), color="#2563eb"); ax1.set_title("Signal (%)")
            ax1.set_ylim(0, 100)
            ax2.plot(xs, list(self.monitor.buf_ping_gw), color="#047857"); ax2.set_title("Gateway Latency (ms)")
            ax3.plot(xs, list(self.monitor.buf_ping_rem), color="#be185d"); ax3.set_title("Internet Latency (ms)")
            fig.tight_layout()
            fig.savefig(buf, format="png")
            data_uri = base64.b64encode(buf.getvalue()).decode('utf-8')
            html.append(f"<img src='data:image/png;base64,{data_uri}' alt='Charts'/>")
            # Diagnostics summary
            html.append("<h2>Diagnostics Summary</h2>")
            html.append("<ul>")
            for sev, iid in sorted(self.current_issues, key=lambda x: x[0], reverse=True):
                entry = self.db.get(iid, {})
                html.append(f"<li><strong>{sev}</strong>: {entry.get('title')}</li>")
            html.append("</ul>")
            # Speed test result
            if self.monitor.last_speed_test is not None:
                html.append("<h2>Speed Test</h2>")
                html.append(f"<p>Download speed: {self.monitor.last_speed_test:.1f} Mbps</p>")
            # Log statistics
            html.append("<h2>Log Statistics</h2>")
            try:
                csv_path = Path(self.config["log_dir"]) / "wifi_log.csv"
                avg_sig = sum([s for s in self.monitor.buf_signal if not math.isnan(s)]) / max(1, len([s for s in self.monitor.buf_signal if not math.isnan(s)]))
                avg_gw_lat = sum([g for g in self.monitor.buf_ping_gw if not math.isnan(g)]) / max(1, len([g for g in self.monitor.buf_ping_gw if not math.isnan(g)]))
                avg_rem_lat = sum([r for r in self.monitor.buf_ping_rem if not math.isnan(r)]) / max(1, len([r for r in self.monitor.buf_ping_rem if not math.isnan(r)]))
                html.append(f"<p>Average signal: {avg_sig:.1f}%</p>")
                html.append(f"<p>Average gateway latency: {avg_gw_lat:.1f} ms</p>")
                html.append(f"<p>Average internet latency: {avg_rem_lat:.1f} ms</p>")
            except Exception:
                pass
            html.append("</body></html>")
            with open(save_path, "w", encoding="utf-8") as f:
                f.write("\n".join(html))
            messagebox.showinfo("Report", f"Report saved to {save_path}")
        except Exception as e:
            messagebox.showerror("Report", f"Failed to generate report: {e}")

    ############################################################################
    # UI update loop
    ############################################################################
    def _ui_update_loop(self) -> None:
        """Periodic UI refresh; schedules itself."""
        # Reschedule
        self.after(1000, self._ui_update_loop)
        # Could add periodic tasks here if needed

    ############################################################################
    # Window close handler
    ############################################################################
    def on_close(self) -> None:
        """Stop background threads and close the application."""
        self._stop_monitor()
        self.destroy()


################################################################################
# Main Entry Point
################################################################################

def main():
    config = load_config()
    db = load_troubleshooting_database()
    app = WiFiGUI(config, db)
    app.mainloop()


if __name__ == "__main__":
    main()