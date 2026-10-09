#!/usr/bin/env python3
"""
🔸 NDX ENGINE V6.0
@NDXCHEATS
Telegram: https://t.me/NDXCHEATS
"""

import itertools as it
import math
import struct
import shutil
import os
import sys
import uuid
import hashlib
import platform
import subprocess
import requests
import base64
import zlib
import ctypes
import webbrowser
from dataclasses import dataclass
from functools import lru_cache
from pathlib import PurePath, Path
from typing import List, Dict, Tuple, Optional, Any
import time
from rich.console import Console
from rich.panel import Panel
from rich.progress import Progress, SpinnerColumn, TextColumn, BarColumn, TaskProgressColumn, TimeElapsedColumn, TimeRemainingColumn
from rich.table import Table
from rich import print as rprint
from rich.markup import escape
from rich.text import Text
from rich.align import Align
from rich.console import Group
from rich.box import HEAVY_EDGE, ROUNDED, DOUBLE_EDGE
from rich.live import Live
from datetime import datetime
import pytz
import gmalg
from Crypto.Cipher import AES
from Crypto.Cipher.AES import MODE_CBC
from Crypto.Hash import SHA1
from Crypto.Util.Padding import unpad
from zstandard import ZstdDecompressor, ZstdCompressionDict, DICT_TYPE_AUTO, ZstdCompressor

# ═══════════════════════════════════════════════════════════════
# CONSTANTS
# ═══════════════════════════════════════════════════════════════

console = Console()

TELEGRAM_LINK = "https://t.me/NDXCHEATS"
LOGIN_FLAG_FILE = ".ndx_login"

ZUC_KEY = bytes.fromhex('01010101010101010101010101010101')
ZUC_IV = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF')

RSA_MOD_1 = bytes.fromhex('CBE8B9F2504050EF9831B719E9A6249A6D238505ADE909BDE78C180DED6072A0C3347B8AF4780E1F212D952D82D4BF7F233C1ECA499E1F9D9A85B4FAD759F54BABC1666C5DE411EA9E4B2374425DD6C6F54333BBC8F2610FE6063E4D0D6C21A671A8F7C3740555E5DC06D4E1691C456DB4116C0C012BF7B206E8311AAAEC689952BF804EF638F09D5822B4117B114208F14DEB459E80CB770E5B0D7978E21F5E6CED4999D3583108221A7AB28B960277ADB5690A332784019D9C195BE4EA9EA0A09459010F236465DE0D59C3EF7324E954E1118D93EE19F299760C2CDB963CE87973EA5ECC9BBE81C27D4C7C8572AC07E9BCEAC9BD72AB7A56A3C0AD736ABCE4')
RSA_MOD_2 = bytes.fromhex('7F58E8A39A4DA4E87357DDD650EAA16D3B5CE95B213D1030A662566444796A78A84AE9AC3DBFFDE7F41094896696835DAF13B89E6EC2B84963B1B1BAF7151DA245C3FBFAE2A6AE18B2684D03F9229DE2C91440F2A3A3BCDE1E5680C16722A88039C73560D5D43F4B6562C2EEA5B1D926D86B51108A2643C70FB74D6442CE3A08339B8FD8F660AE88129B7AB8C46F2FA58124485CCCB1E987B05A6DA65A01858ED3F89905449AE42BB07290FCB9994BF22E26610BCABB9804783A3B9587917F3D97316EDDA15C5E13F79066407B55A93B291B68A4AC42A98D6E35FED84B14A792D154E62028DDAD20FC301951E5924BE9AD62FB719DD94CC30CAB871BEC4377A8')

SIMPLE1_DECRYPT_KEY = 121
SIMPLE2_DECRYPT_KEY = bytes.fromhex('E55B4ED1')
SIMPLE2_BLOCK_SIZE = 16

SM4_SECRET_4 = 'eb691efea914241317a8'
SM4_SECRET_2 = 'Q0hVTKey$as*1ZFlQCiA'
SM4_SECRET_NEW = [
    'xG2qW5lP7lV2iN5fN5pG', 'xT1cJ6dL5wC0kK1rB4dK', 'qC4jS5bZ6fL5xE6nD4zA',
    'gD4jQ2aL3bS3lC3xT0iW', 'xU1yQ8wE9zY3gZ3bT5aE', 'uQ3cO2dX7xY4xU7gH7iS',
    'gW1fR0jK6wQ4oN0oK1kZ', 'aJ4pV7iZ7pU4wP2aC2cZ', 'cX6jT3cM2oT3vK0kJ1qN',
    'iT2vS0cS6yT6cZ1sE1lO', 'hM1pH9iY8wM9hT4lN5uJ', 'kG6bC8jK0fL0dE4sH4mL',
    'dB6lB3vE0eZ8wM8rI0aC', 'tP7sP7nI9rA2vQ4cV5yQ', 'aT0cL1yN4pT3sZ7eM2vY',
    'uV6fU8fC9zN3mP5dH8mN', 'rT6aQ6oZ1yM0gO5tO1aN', 'jU5bH7lQ0fM9hK2kI0oF',
    'iQ0eM0mJ7uT0kV6kL5zY',
]

EM_SIMPLE1 = 1
EM_SIMPLE2 = 16
EM_SM4_2 = 2
EM_SM4_4 = 4
EM_SM4_NEW_BASE = 31
EM_SM4_NEW_MASK = ~EM_SM4_NEW_BASE
EM_UNKNOWN_17 = 17

CM_NONE = 0
CM_ZLIB = 1
CM_ZSTD = 6
CM_ZSTD_DICT = 8
CM_MASK = 15


# ═══════════════════════════════════════════════════════════════
# FILE ENCRYPT / DECRYPT (AES-256-GCM)
# ═══════════════════════════════════════════════════════════════

FILE_CRYPT_MAGIC = b"NDXE2"
FILE_CRYPT_SALT_SIZE = 16
FILE_CRYPT_NONCE_SIZE = 12
FILE_CRYPT_TAG_SIZE = 16
FILE_CRYPT_KDF_ROUNDS = 200_000


def _derive_file_key(salt: bytes) -> bytes:
    """Derive a built-in key; the Encrypt/Decrypt menu does not ask for a password."""
    # Convenience mode: the same internal key is used for encrypt/decrypt.
    # This intentionally removes the password prompt, so anyone with the tool
    # can decrypt files produced by this tool.
    internal_secret = b"NDX_ENGINE_V6_FILE_CRYPT"
    return hashlib.sha256(internal_secret + salt).digest()


def encrypt_file_secure(input_path: Path, output_path: Path):
    """Encrypt the complete file byte-for-byte, using bounded-memory streaming."""
    salt = os.urandom(FILE_CRYPT_SALT_SIZE)
    nonce = os.urandom(FILE_CRYPT_NONCE_SIZE)
    key = _derive_file_key(salt)
    cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
    cipher.update(FILE_CRYPT_MAGIC)

    output_path.parent.mkdir(parents=True, exist_ok=True)
    temp_path = output_path.with_name(output_path.name + ".tmp")
    try:
        with input_path.open("rb") as src, temp_path.open("wb") as dst:
            dst.write(FILE_CRYPT_MAGIC)
            dst.write(salt)
            dst.write(nonce)

            while True:
                chunk = src.read(1024 * 1024)
                if not chunk:
                    break
                dst.write(cipher.encrypt(chunk))

            tag = cipher.digest()
            dst.write(tag)
            dst.flush()
            os.fsync(dst.fileno())

        os.replace(temp_path, output_path)
    except Exception:
        try:
            temp_path.unlink(missing_ok=True)
        except Exception:
            pass
        raise


def decrypt_file_secure(input_path: Path, output_path: Path):
    """Decrypt the complete file byte-for-byte and verify the GCM tag first."""
    header_size = len(FILE_CRYPT_MAGIC) + FILE_CRYPT_SALT_SIZE + FILE_CRYPT_NONCE_SIZE + FILE_CRYPT_TAG_SIZE
    file_size = input_path.stat().st_size
    if file_size < header_size:
        raise ValueError("Unsupported/encrypted file format")

    temp_path = output_path.with_name(output_path.name + ".tmp")
    try:
        with input_path.open("rb") as src:
            magic = src.read(len(FILE_CRYPT_MAGIC))
            if magic != FILE_CRYPT_MAGIC:
                raise ValueError("Unsupported/encrypted file format")

            salt = src.read(FILE_CRYPT_SALT_SIZE)
            nonce = src.read(FILE_CRYPT_NONCE_SIZE)
            if len(salt) != FILE_CRYPT_SALT_SIZE or len(nonce) != FILE_CRYPT_NONCE_SIZE:
                raise ValueError("Encrypted file header is incomplete")

            key = _derive_file_key(salt)
            cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
            cipher.update(FILE_CRYPT_MAGIC)

            # The final 16 bytes are the authentication tag. Stream only the ciphertext.
            remaining = file_size - (len(FILE_CRYPT_MAGIC) + FILE_CRYPT_SALT_SIZE + FILE_CRYPT_NONCE_SIZE + FILE_CRYPT_TAG_SIZE)
            with temp_path.open("wb") as dst:
                while remaining:
                    take = min(1024 * 1024, remaining)
                    chunk = src.read(take)
                    if len(chunk) != take:
                        raise ValueError("Encrypted file is truncated")
                    dst.write(cipher.decrypt(chunk))
                    remaining -= take

                tag = src.read(FILE_CRYPT_TAG_SIZE)
                if len(tag) != FILE_CRYPT_TAG_SIZE:
                    raise ValueError("Encrypted file is truncated")

                try:
                    cipher.verify(tag)
                except ValueError:
                    raise ValueError("Encrypted file is corrupted or incompatible")

                dst.flush()
                os.fsync(dst.fileno())

        os.replace(temp_path, output_path)
    except Exception:
        try:
            temp_path.unlink(missing_ok=True)
        except Exception:
            pass
        raise

def _crypto_dirs(data_path: Path):
    """Create isolated input/output folders for Lua crypto operations."""
    dirs = {
        "encrypt_input": data_path / "ENCRYPT_INPUT",
        "encrypt_output": data_path / "ENCRYPT_OUTPUT",
        "decrypt_input": data_path / "DECRYPT_INPUT",
        "decrypt_output": data_path / "DECRYPT_OUTPUT",
    }
    for folder in dirs.values():
        folder.mkdir(parents=True, exist_ok=True)
    return dirs


def _select_crypto_file(data_path: Path, is_decrypt: bool):
    """Show only files placed in the selected operation's INPUT folder."""
    dirs = _crypto_dirs(data_path)
    input_dir = dirs["decrypt_input"] if is_decrypt else dirs["encrypt_input"]
    pattern = "*.ndxenc" if is_decrypt else "*.lua"
    files = sorted(
        [p for p in input_dir.glob(pattern) if p.is_file()],
        key=lambda x: x.name.lower(),
    )

    action = "DECRYPT" if is_decrypt else "ENCRYPT"
    input_label = "DECRYPT_INPUT" if is_decrypt else "ENCRYPT_INPUT"
    output_label = "DECRYPT_OUTPUT" if is_decrypt else "ENCRYPT_OUTPUT"

    console.print()
    console.print(f"[bold bright_cyan]╭─ {action} FILE SELECT ─────────────────────────────╮[/]")
    console.print(f"[bold bright_cyan]│[/] [bold bright_yellow]INPUT : {input_label}/[/]")
    console.print(f"[bold bright_cyan]│[/] [bold bright_green]OUTPUT: {output_label}/[/]")
    console.print("[bold bright_cyan]╰──────────────────────────────────────────────────────╯[/]")
    console.print()

    if not files:
        label = ".ndxenc" if is_decrypt else ".lua"
        console.print(f"[bold bright_yellow]📂 Put your {label} file(s) inside {input_label}/[/]")
        console.print(f"[dim]Output will be created automatically in {output_label}/[/]")
        console.print()
        console.print("[bold bright_yellow]00[/]  [bold bright_magenta]↩ BACK[/]")
        console.print()
        safe_input("[bold bright_yellow]Press Enter to return...[/]")
        return None

    for i, file_path in enumerate(files, 1):
        size = human_size(file_path.stat().st_size)
        console.print(
            f"[bold bright_yellow]{i:02d}[/]  [bold bright_green]📄 {file_path.name}[/] "
            f"[dim]({size})[/]"
        )

    console.print()
    console.print("[bold bright_yellow]00[/]  [bold bright_magenta]↩ BACK[/]")
    console.print()

    while True:
        choice = safe_input(f"SELECT FILE (1-{len(files)}) / 0-BACK: ").strip()
        if choice == "0":
            return None
        try:
            idx = int(choice) - 1
        except ValueError:
            console.print("[bold bright_red]✗ Enter a file number.[/]")
            continue
        if 0 <= idx < len(files):
            return files[idx]
        console.print("[bold bright_red]✗ Invalid file number.[/]")


def file_encrypt_decrypt_menu(data_path: Path):
    """Lua encryption/decryption with separate input and output folders."""
    dirs = _crypto_dirs(data_path)

    while True:
        print_banner()
        console.print()
        console.print("   [bold bright_cyan]╔══════════════════════════════════════════════════╗[/]")
        console.print("   [bold bright_magenta]║               🔒 LUA ENCRYPTOR                 ║[/]")
        console.print("   [bold bright_yellow]║          AES-256-GCM • NO PASSWORD             ║[/]")
        console.print("   [bold bright_cyan]╚══════════════════════════════════════════════════╝[/]")
        console.print()
        console.print("   [bold bright_green]01[/]  🔒 ENCRYPT LUA")
        console.print("        [dim]Input : ENCRYPT_INPUT/   →   Output: ENCRYPT_OUTPUT/[/]")
        console.print("   [bold bright_yellow]00[/]  ↩ BACK TO MAIN MENU")
        console.print()

        choice = safe_input("[bold bright_magenta]◆ SELECT OPTION (1 / 0): [/]").strip().lower()
        if choice in ("0", "b", "back", "2"):
            return
        if choice != "1":
            console.print("[bold bright_red]✗ Choose 1 to encrypt or 0 to go back.[/]")
            time.sleep(0.9)
            continue

        is_decrypt = False
        selected = _select_crypto_file(data_path, is_decrypt)
        if not selected:
            continue

        action = "DECRYPT" if is_decrypt else "ENCRYPT"
        try:
            console.print()
            console.print(f"[bold bright_cyan]⚡ {action}: {selected.name}[/]")

            if is_decrypt:
                output_dir = dirs["decrypt_output"]
                output_name = selected.name[:-len(".ndxenc")]
                output = output_dir / output_name
                if output.exists():
                    output = output_dir / f"{Path(output_name).stem}.decrypted{Path(output_name).suffix}"
                decrypt_file_secure(selected, output)
            else:
                output_dir = dirs["encrypt_output"]
                output = output_dir / f"{selected.name}.ndxenc"
                if output.exists():
                    output = output_dir / f"{selected.stem}.new{selected.suffix}.ndxenc"
                encrypt_file_secure(selected, output)

            console.print("[bold bright_green]✓ SUCCESS — Complete file processed without truncation.[/]")
            console.print(f"[bold bright_cyan]📁 OUTPUT: {output}[/]")
        except Exception as e:
            console.print(f"[bold bright_red]❌ {action} FAILED: {escape(str(e))}[/]")

        safe_input("[bold bright_yellow]Press Enter to continue...[/]")


# ═══════════════════════════════════════════════════════════════
# UTILITIES
# ═══════════════════════════════════════════════════════════════
def _term_width(default=80):
    try:
        return shutil.get_terminal_size((default, 24)).columns
    except Exception:
        return default


def get_indian_time():
    tz = pytz.timezone("Asia/Kolkata")
    return datetime.now(tz).strftime("%d-%m-%Y  %I:%M:%S %p")


def print_decorative_separator(char="─", color="bright_cyan", length=60):
    w = _term_width()
    length = min(length, w - 2)
    console.print(Text(char * length, style=f"bold {color}"))


def human_size(size: int) -> str:
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if size < 1024.0:
            return f'{size:.2f} {unit}'
        size /= 1024.0
    return f'{size:.2f} PB'


def safe_input(prompt: str = '') -> str:
    w = _term_width()
    try:
        if w < 45:
            short_prompt = prompt[:max(1, w - 8)]
            console.print(f"[bold bright_cyan]🔸 {short_prompt}[/]", end="")
        else:
            console.print(f"\n[bold bright_cyan]🔸 [/][bold bright_magenta]{prompt}[/]", end="")
        return input()
    except (EOFError, RuntimeError):
        try:
            if sys.platform != 'win32':
                with open('/dev/tty', 'r') as tty:
                    sys.stderr.write(f"\n🔸 {prompt}")
                    sys.stderr.flush()
                    return tty.readline().rstrip('\n')
            else:
                with open('CON', 'r') as con:
                    sys.stderr.write(f"\n🔸 {prompt}")
                    sys.stderr.flush()
                    return con.readline().rstrip('\r\n')
        except Exception:
            return ''
    except Exception:
        return ''


# ═══════════════════════════════════════════════════════════════
# FIREBASE LOGIN SYSTEM
# ═══════════════════════════════════════════════════════════════

FIREBASE_URL = "https://ndx-engine-default-rtdb.firebaseio.com"


def _login_flag_path() -> Path:
    if getattr(sys, 'frozen', False):
        base = Path(sys.executable).parent
    else:
        base = Path(__file__).parent
    return base / LOGIN_FLAG_FILE


def is_logged_in() -> bool:
    return _login_flag_path().exists()


def save_login(user_key: str = ""):
    try:
        _login_flag_path().write_text(
            f"@NDXCHEATS\n"
            f"key={user_key}\n"
            f"logged_in_at={int(time.time())}\n",
            encoding="utf-8"
        )
    except Exception:
        pass


def clear_login():
    try:
        p = _login_flag_path()
        if p.exists():
            p.unlink()
    except Exception:
        pass


def firebase_check_key(user_key: str) -> bool:
    """
    Firebase Realtime Database से key verify करता है।
    URL: {FIREBASE_URL}/keys/{user_key}.json

    Supported formats:
      - true / false (boolean)
      - {"active": true/false, "expiry": "YYYY-MM-DD"}
      - string value
    """
    if not user_key or len(user_key.strip()) < 8:
        return False

    user_key = user_key.strip()
    url = f"{FIREBASE_URL}/keys/{user_key}.json"

    try:
        r = requests.get(url, timeout=10)
        if r.status_code != 200:
            console.print(f"[bold bright_red]❌ Firebase error (HTTP {r.status_code})[/]")
            return False

        data = r.json()

        if data is None:
            return False

        if data is True:
            return True

        if isinstance(data, str):
            return data.lower() in ("true", "active", "valid", "1", "yes")

        if isinstance(data, dict):
            if data.get("active") is True:
                pass
            elif data.get("valid") is True:
                pass
            elif data.get("status") in ("active", "valid", "true"):
                pass
            elif data.get("banned") is True:
                return False
            elif data.get("active") is False:
                return False
            else:
                pass

            expiry = data.get("expiry") or data.get("expires")
            if expiry:
                try:
                    from datetime import datetime as _dt
                    exp_date = _dt.strptime(str(expiry).split("T")[0], "%Y-%m-%d")
                    if _dt.now() > exp_date:
                        return False
                except Exception:
                    pass

            return True

        if isinstance(data, (int, float)):
            return data == 1

        return False

    except requests.exceptions.Timeout:
        console.print("[bold bright_red]❌ Firebase timeout — internet check karein[/]")
        return False
    except requests.exceptions.ConnectionError:
        console.print("[bold bright_red]❌ No internet connection![/]")
        return False
    except Exception as e:
        console.print(f"[bold bright_red]❌ Firebase error: {escape(str(e))}[/]")
        return False


def show_live_key_expiry():
    """Fetch key status from Firebase and display exact expiry date/time and time left.

    Supports Unix timestamps (seconds or milliseconds), ISO-8601 datetimes,
    and YYYY-MM-DD dates (treated as valid through 23:59:59 local time).
    """
    from datetime import datetime as _dt, date as _date, time as _time, timedelta as _td
    import math as _math

    try:
        p = _login_flag_path()
        if not p.exists():
            console.print("[bold bright_red]✗ No active login session.[/]")
            safe_input("\nPress Enter to return...")
            return

        key = ""
        for line in p.read_text(encoding="utf-8", errors="ignore").splitlines():
            if line.startswith("key="):
                key = line[4:].strip()
                break
        if not key:
            console.print("[bold bright_red]✗ Login key not found in session.[/]")
            safe_input("\nPress Enter to return...")
            return

        console.print()
        console.print(Align.center(Text("╔════════════════════════════════════════════╗", style="bold bright_cyan")))
        console.print(Align.center(Text("║        🔑 LIVE KEY / EXPIRY STATUS        ║", style="bold bright_magenta")))
        console.print(Align.center(Text("╚════════════════════════════════════════════╝", style="bold bright_cyan")))
        console.print()

        with console.status("[bold bright_green]🔄 Fetching live data from Firebase...", spinner="dots"):
            r = requests.get(f"{FIREBASE_URL}/keys/{key}.json", timeout=10)
        if r.status_code != 200:
            console.print(f"[bold bright_red]✗ Firebase error (HTTP {r.status_code})[/]")
            safe_input("\nPress Enter to return...")
            return

        data = r.json()
        if data is None:
            console.print("[bold bright_red]✗ Key no longer exists on Firebase.[/]")
            safe_input("\nPress Enter to return...")
            return

        active = True
        expiry = None
        if isinstance(data, dict):
            active = not (data.get("banned") is True or data.get("active") is False
                          or str(data.get("status", "")).lower() in ("banned", "disabled", "inactive"))
            expiry = data.get("expiry") or data.get("expires") or data.get("expires_at") or data.get("expiry_timestamp")
        elif data is False or (isinstance(data, (int, float)) and not isinstance(data, bool) and data == 0):
            active = False

        console.print(f"[bold bright_cyan]🔑 KEY:[/] [bold bright_yellow]{key}[/]")
        console.print("[bold bright_cyan]● STATUS:[/] " + ("[bold bright_green]ACTIVE[/]" if active else "[bold bright_red]INACTIVE / BANNED[/]"))

        if expiry is None or expiry == "":
            console.print("[bold bright_cyan]📅 EXPIRY:[/] [bold bright_yellow]NO EXPIRY SET[/]")
        else:
            exp_dt = None
            raw = expiry
            try:
                # Numeric Firebase values are usually Unix timestamps; accept ms too.
                if isinstance(raw, (int, float)) or (isinstance(raw, str) and raw.strip().isdigit()):
                    stamp = float(raw)
                    if stamp > 100000000000:
                        stamp /= 1000.0
                    exp_dt = _dt.fromtimestamp(stamp).astimezone()
                else:
                    value = str(raw).strip()
                    try:
                        exp_dt = _dt.fromisoformat(value.replace("Z", "+00:00"))
                        if exp_dt.tzinfo is not None:
                            exp_dt = exp_dt.astimezone()
                        else:
                            exp_dt = exp_dt.astimezone()
                    except ValueError:
                        # A date-only expiry is valid through the end of that local day.
                        day = _dt.strptime(value[:10], "%Y-%m-%d").date()
                        exp_dt = _dt.combine(day, _time(23, 59, 59)).astimezone()

                now = _dt.now().astimezone()
                seconds_left = int((exp_dt - now).total_seconds())
                console.print(f"[bold bright_cyan]📅 EXPIRES AT:[/] [bold bright_white]{exp_dt.strftime('%d-%m-%Y %I:%M:%S %p %Z')}[/]")
                if seconds_left <= 0:
                    console.print("[bold bright_red]⛔ EXPIRED[/]")
                else:
                    days, rem = divmod(seconds_left, 86400)
                    hours, rem = divmod(rem, 3600)
                    minutes, seconds = divmod(rem, 60)
                    console.print(f"[bold bright_cyan]⏳ TIME LEFT:[/] [bold bright_green]{days} days, {hours} hours, {minutes} minutes, {seconds} seconds[/]")
            except (ValueError, TypeError, OverflowError, OSError):
                console.print(f"[bold bright_cyan]📅 EXPIRY:[/] [bold bright_red]Unsupported expiry format:[/] {escape(str(expiry))}")
                console.print("[dim]Use Unix timestamp (seconds/milliseconds), ISO datetime, or YYYY-MM-DD.[/]")

        console.print()
        console.print("[dim]Live status fetched from Firebase; countdown is calculated using this device's local time.[/]")
        safe_input("\n[bold bright_yellow]Press Enter to return to Main Menu...[/]")
    except requests.exceptions.Timeout:
        console.print("[bold bright_red]✗ Firebase timeout.[/]")
        safe_input("\nPress Enter to return...")
    except requests.exceptions.ConnectionError:
        console.print("[bold bright_red]✗ No internet connection.[/]")
        safe_input("\nPress Enter to return...")
    except Exception as e:
        console.print(f"[bold bright_red]✗ Error: {escape(str(e))}[/]")
        safe_input("\nPress Enter to return...")


def show_login_screen():
    w = _term_width()
    os.system('cls' if os.name == 'nt' else 'clear')

    if w < 45:
        console.print()
        console.print("[bold bright_cyan]╔══════════════════════════════╗[/]")
        console.print("[bold bright_cyan]║[/]  [bold bright_magenta]🔸 NDX ENGINE V6.0 🔸[/]      [bold bright_cyan]║[/]")
        console.print("[bold bright_cyan]║[/]  [bold bright_yellow]   FIREBASE LOGIN[/]          [bold bright_cyan]║[/]")
        console.print("[bold bright_yellow]╚══════════════════════════════╝[/]")
        console.print()
        console.print(Align.center(Text("ENTER YOUR ACCESS KEY", style="bold bright_yellow")))
        console.print()
        console.print(Align.center(Text("@NDXCHEATS", style="bold bright_magenta")))
        console.print()
        return

    console.print()
    console.print(Align.center(
        Text("╭─ 🔸 ─────────────────────────────────────── 🔸 ─╮", style="bold bright_cyan")
    ))
    console.print(Align.center(
        Text("│                                                │", style="bold blue")
    ))
    console.print(Align.center(
        Text("│           🔸 NDX ENGINE V6.0 🔸                │", style="bold bright_magenta")
    ))
    console.print(Align.center(
        Text("│                @NDXCHEATS                      │", style="bold bright_yellow")
    ))
    console.print(Align.center(
        Text("│                                                │", style="bold bright_green")
    ))
    console.print(Align.center(
        Text("│              FIREBASE LOGIN                    │", style="bold bright_red")
    ))
    console.print(Align.center(
        Text("│                                                │", style="bold bright_green")
    ))
    console.print(Align.center(
        Text("╰─ 🔸 ─────────────────────────────────────── 🔸 ─╯", style="bold bright_magenta")
    ))
    console.print()

    login_panel = Panel(
        Group(
            Text("", justify="center"),
            Text("🔐  ENTER YOUR ACCESS KEY", style="bold bright_white", justify="center"),
            Text("", justify="center"),
            Text("Key Firebase server se verify hogi", style="dim white", justify="center"),
            Text("", justify="center"),
        ),
        border_style="bold bright_green",
        box=ROUNDED,
        padding=(0, 2),
        width=62,
    )
    console.print(Align.center(login_panel))
    console.print()


def prompt_login():
    """Firebase-based key login"""
    show_login_screen()

    max_attempts = 5
    attempt = 0

    while attempt < max_attempts:
        attempt += 1

        console.print(Align.center(
            Text(f"🔸 Attempt {attempt}/{max_attempts}", style="bold bright_yellow")
        ))
        console.print()

        try:
            user_key = safe_input("ENTER ACCESS KEY: ").strip()
        except Exception:
            user_key = ""

        if not user_key:
            console.print()
            console.print(Align.center(
                Text("⚠ Key khali nahi ho sakti!", style="bold bright_red")
            ))
            console.print()
            time.sleep(1.2)
            continue

        console.print()
        with console.status("[bold bright_green]🔸 Verifying with Firebase...", spinner="dots"):
            time.sleep(0.6)
            is_valid = firebase_check_key(user_key)

        if is_valid:
            save_login(user_key)
            console.print()
            console.print(Align.center(
                Text("✓ LOGIN SUCCESSFUL", style="bold bright_green")
            ))
            console.print(Align.center(
                Text("WELCOME TO NDX ENGINE V6.0", style="bold bright_magenta")
            ))
            console.print()
            time.sleep(1.3)
            return True
        else:
            console.print()
            console.print(Align.center(
                Text("✗ INVALID KEY — ACCESS DENIED", style="bold bright_red")
            ))
            console.print(Align.center(
                Text("@NDXCHEATS par contact karein", style="bold bright_yellow")
            ))
            console.print()
            time.sleep(1.5)

    console.print()
    console.print(Align.center(
        Text("❌ TOO MANY FAILED ATTEMPTS", style="bold bright_red")
    ))
    console.print(Align.center(
        Text("Telegram: https://t.me/NDXCHEATS", style="bold bright_cyan")
    ))
    console.print()
    safe_input("Press Enter to exit...")
    sys.exit(1)


# ═══════════════════════════════════════════════════════════════
# SIMPLE BLOCK DISPLAY
# ═══════════════════════════════════════════════════════════════

class SimpleBlockDisplay:
    def __init__(self, total_files: int, pak_name: str):
        self.total_files = total_files
        self.pak_name = pak_name
        self.processed_files = 0
        self.current_file = ""
        self.current_file_idx = 0
        self.all_blocks = []
        self.total_fitted = 0
        self.total_skipped = 0
        self.session_start = time.time()

    def start_file(self, file_name: str, total_blocks: int):
        self.current_file_idx += 1
        self.current_file = file_name
        self.current_total_blocks = total_blocks
        self.current_fitted = 0
        self.current_skipped = 0
        self.current_blocks = []

        name = file_name if len(file_name) <= 28 else file_name[:25] + "..."
        blocks_txt = f"{total_blocks} block{'s' if total_blocks != 1 else ''}"

        console.print()
        console.print("╭" + "─" * 58 + "╮", style="bold bright_cyan")
        left = f"  🔸 [{self.current_file_idx}/{self.total_files}]  {name}"
        gap = 58 - len(left) - len(blocks_txt) - 1
        gap = max(gap, 1)
        console.print(
            f"[bold bright_cyan]│[/]"
            f"[bold bright_yellow]  🔸 [{self.current_file_idx}/{self.total_files}][/]"
            f"  [bold bright_green]{name}[/]"
            f"{' ' * gap}"
            f"[bold bright_white]{blocks_txt}[/]"
            f"[bold bright_cyan]│[/]"
        )
        console.print("├" + "─" * 58 + "┤", style="bold bright_cyan")

    def add_block(self, block_idx: int, block_size: int, fitted: bool,
                  compression_ratio: float = None):
        size_mb = block_size / (1024 * 1024)

        if fitted and compression_ratio is not None:
            filled = int(compression_ratio * 10)
            bar = "▰" * filled + "▱" * (10 - filled)
            bar_style = "bold bright_green"
            ratio_txt = f"{compression_ratio:.0%}"
            status = "[bold bright_green]✓[/]"
            num_style = "bold bright_green"
        elif fitted:
            bar = "▰" * 10
            bar_style = "bold bright_green"
            ratio_txt = "100%"
            status = "[bold bright_green]✓[/]"
            num_style = "bold bright_green"
        else:
            bar = "▱" * 10
            bar_style = "bold bright_red"
            ratio_txt = " -- "
            status = "[bold bright_red]✗[/]"
            num_style = "bold bright_red"

        line = (
            f"   [{num_style}]● {block_idx + 1:02d}[/]  "
            f"[bold bright_white]{size_mb:>7.2f} MB[/]  "
            f"[{bar_style}]{bar}[/]  "
            f"[bold bright_yellow]{ratio_txt:>4}[/]  "
            f"{status}"
        )
        console.print(f"[bold bright_cyan]│[/]{line}   [bold bright_cyan]│[/]")

        if fitted:
            self.current_fitted += 1
            self.total_fitted += 1
        else:
            self.current_skipped += 1
            self.total_skipped += 1

        self.current_blocks.append({'fitted': fitted})

    def finish_file(self):
        total_blocks = len(self.current_blocks)

        if total_blocks == 0:
            result = "[bold bright_green]✓ DONE[/]"
            rate = 100.0
            dot = "🟢"
        else:
            rate = (self.current_fitted / total_blocks) * 100
            if rate == 100:
                result = f"[bold bright_green]✓ Fitted: {self.current_fitted}/{total_blocks}[/]"
                dot = "🟢"
            elif rate >= 50:
                result = f"[bold bright_yellow]✓ Fitted: {self.current_fitted}/{total_blocks}[/]"
                dot = "🟡"
            else:
                result = f"[bold bright_red]✗ Fitted: {self.current_fitted}/{total_blocks}[/]"
                dot = "🔴"

        console.print("├" + "─" * 58 + "┤", style="bold bright_cyan")

        rate_txt = f"{dot} {rate:.1f}%"
        plain_result = f"  ✓ Fitted: {self.current_fitted}/{total_blocks}" if total_blocks else "  ✓ DONE"
        gap = 58 - len(plain_result) - len(f" {rate_txt} ")
        gap = max(gap, 1)

        console.print(
            f"[bold bright_cyan]│[/]"
            f"{result}"
            f"{' ' * gap}"
            f"[bold bright_magenta]{rate_txt}[/]"
            f"[bold bright_cyan]│[/]"
        )
        console.print("╰" + "─" * 58 + "╯", style="bold bright_cyan")
        console.print()

        self.processed_files += 1
        self.all_blocks.extend(self.current_blocks)

    def final_summary(self):
        total_blocks = len(self.all_blocks)
        duration = time.time() - self.session_start
        mins, secs = divmod(int(duration), 60)
        rate = (self.total_fitted / total_blocks * 100) if total_blocks else 0

        if rate >= 80:
            border = "bold bright_green"
            dot = "🟢"
        elif rate >= 50:
            border = "bold bright_yellow"
            dot = "🟡"
        else:
            border = "bold bright_red"
            dot = "🔴"

        filled = int(rate / 100 * 24)
        overall_bar = "▰" * filled + "▱" * (24 - filled)

        summary = Panel(
            Group(
                Text(""),
                Align.center(Text("📊  REPACK SUMMARY", style="bold bright_magenta")),
                Text(""),
                Align.center(Text(overall_bar, style=border)),
                Align.center(Text(f"{dot}  {rate:.1f}% SUCCESS", style=border)),
                Text(""),
                Text("─" * 52, style="bold bright_cyan", justify="center"),
                Text(""),
                Text.from_markup(f"   🔸  Files      :  [bold bright_cyan]{self.processed_files}/{self.total_files}[/]"),
                Text.from_markup(f"   🔸  Blocks     :  [bold bright_cyan]{total_blocks}[/]"),
                Text.from_markup(f"   ✓   Fitted     :  [bold bright_green]{self.total_fitted}[/]"),
                Text.from_markup(f"   ✗   Skipped    :  [bold bright_red]{self.total_skipped}[/]"),
                Text.from_markup(f"   🔸  Time       :  [bold bright_yellow]{mins}m {secs}s[/]"),
                Text.from_markup(f"   🔸  PAK        :  [bold bright_magenta]{self.pak_name}[/]"),
                Text.from_markup(f"   🔸  Dev        :  [bold bright_magenta]@NDXCHEATS[/]"),
                Text(""),
            ),
            border_style=border,
            box=DOUBLE_EDGE,
            padding=(1, 3),
            title="[bold bright_magenta]🔸 NDX ENGINE 🔸[/]",
            title_align="center",
        )
        console.print(summary)
        console.print()


# ═══════════════════════════════════════════════════════════════
# UNPACK PROGRESS UI
# ═══════════════════════════════════════════════════════════════

class UnpackProgressUI:
    PANEL_W = 58

    def __init__(self, pak_name: str, output_dir: str, total_files: int):
        self.pak_name = pak_name
        self.output_dir = str(output_dir)
        self.total_files = total_files
        self.current_file = ""
        self.extracted = 0
        self.start_time = time.time()
        self.live = None

    def _render(self):
        pct = (self.extracted / self.total_files * 100) if self.total_files else 0

        # Colourful 7-section progress bar
        # Each completed section gets a different colour, matching the
        # new rainbow-style progress design while keeping the UI compact.
        bar_width = 33
        filled = int(pct / 100 * bar_width)
        colors = [
            "bright_red", "bright_yellow", "bright_green",
            "bright_cyan", "bright_blue", "bright_magenta", "white"
        ]
        segments = []
        for i, color in enumerate(colors):
            start = (i * bar_width) // 7
            end = ((i + 1) * bar_width) // 7
            segment_len = end - start
            completed = max(0, min(segment_len, filled - start))
            if completed:
                segments.append(f"[bold {color}]{'█' * completed}[/]")
            if completed < segment_len:
                segments.append(f"[dim]{'░' * (segment_len - completed)}[/]")
        bar = "".join(segments)
        bar_style = "bold bright_cyan"

        elapsed = time.time() - self.start_time
        mins, secs = divmod(int(elapsed), 60)
        rate = self.extracted / elapsed if elapsed > 0 else 0
        remaining = self.total_files - self.extracted
        eta_secs = int(remaining / rate) if rate > 0 else 0
        eta_m, eta_s = divmod(eta_secs, 60)

        cur = self.current_file
        if len(cur) > 48:
            cur = "..." + cur[-45:]

        L = []
        l1 = f"  {self.pak_name}  →  {self.output_dir}"
        if len(l1) > 56:
            l1 = l1[:53] + "..."
        L.append(f"[bold bright_cyan]│[/][bold bright_yellow]{l1}[/]{' ' * (58 - len(l1))}[bold bright_cyan]│[/]")
        L.append(f"[bold bright_cyan]│[/]{' ' * 58}[bold bright_cyan]│[/]")

        pct_txt = f"{pct:.0f}%"
        bar_line = f"  {bar}  [bold bright_white]{pct_txt}[/]"
        plain_w = 2 + 33 + 2 + len(pct_txt)
        L.append(f"[bold bright_cyan]│[/]{bar_line}{' ' * (58 - plain_w)}[bold bright_cyan]│[/]")
        L.append(f"[bold bright_cyan]│[/]{' ' * 58}[bold bright_cyan]│[/]")

        f_line = f"  🔸 {cur}"
        pad = 58 - len(f_line)
        L.append(f"[bold bright_cyan]│[/][bold bright_white]{f_line}[/]{' ' * max(pad,0)}[bold bright_cyan]│[/]")

        c_line = f"  🔸 {self.extracted:,} / {self.total_files:,} files"
        pad = 58 - len(c_line)
        L.append(f"[bold bright_cyan]│[/][bold bright_cyan]{c_line}[/]{' ' * max(pad,0)}[bold bright_cyan]│[/]")

        e_line = f"  🔸 Elapsed: {mins:02d}:{secs:02d}   🔸 ETA: {eta_m:02d}:{eta_s:02d}"
        pad = 58 - len(e_line)
        L.append(f"[bold bright_cyan]│[/][bold bright_yellow]{e_line}[/]{' ' * max(pad,0)}[bold bright_cyan]│[/]")

        s_line = f"  🔸 Speed: {rate:,.0f} files/s"
        pad = 58 - len(s_line)
        L.append(f"[bold bright_cyan]│[/][bold bright_green]{s_line}[/]{' ' * max(pad,0)}[bold bright_cyan]│[/]")

        top = "[bold bright_cyan]╭─ 🔸 UNPACKING " + "─" * (58 - 16) + "╮[/]"
        bot = "[bold bright_cyan]╰" + "─" * 58 + "╯[/]"
        body = "\n".join(L)
        return Text.from_markup(f"{top}\n{body}\n{bot}")

    def start(self):
        self.live = Live(self._render(), console=console, refresh_per_second=8)
        self.live.start()

    def update(self, file_name: str = None):
        if file_name:
            self.current_file = file_name
            self.extracted += 1
        if self.live:
            self.live.update(self._render())

    def stop(self):
        if self.live:
            self.extracted = self.total_files
            self.current_file = "Done ✓"
            self.live.update(self._render())
            time.sleep(0.3)
            self.live.stop()
            self.live = None


# ═══════════════════════════════════════════════════════════════
# SM4
# ═══════════════════════════════════════════════════════════════

class SM4:
    _S_BOX = bytes([
        52, 102, 37, 116, 137, 120, 228, 169, 90, 65, 188, 122, 214, 22, 33, 35,
        77, 97, 218, 148, 155, 223, 19, 60, 105, 58, 49, 10, 95, 215, 153, 149,
        241, 174, 114, 61, 7, 96, 36, 182, 152, 238, 196, 162, 45, 136, 221, 141,
        4, 234, 187, 17, 202, 62, 93, 161, 246, 63, 176, 151, 128, 71, 43, 166,
        230, 247, 217, 177, 89, 192, 124, 190, 84, 40, 183, 126, 79, 248, 67, 110,
        160, 80, 14, 245, 144, 184, 251, 163, 123, 98, 25, 70, 3, 42, 185, 143,
        159, 119, 180, 91, 131, 135, 8, 235, 226, 30, 66, 240, 15, 232, 113, 106,
        117, 173, 85, 31, 181, 171, 51, 250, 127, 21, 189, 133, 216, 6, 104, 179,
        82, 48, 72, 11, 0, 237, 239, 178, 87, 142, 231, 108, 213, 229, 46, 83,
        130, 5, 249, 129, 244, 86, 191, 140, 75, 227, 219, 74, 145, 76, 44, 211,
        64, 41, 78, 32, 20, 54, 121, 9, 111, 209, 55, 224, 57, 12, 138, 146,
        56, 18, 53, 109, 225, 253, 147, 154, 23, 212, 201, 156, 107, 132, 38, 157,
        175, 118, 193, 158, 208, 150, 197, 203, 233, 115, 73, 210, 205, 100, 195, 199,
        1, 125, 243, 172, 252, 222, 164, 68, 50, 27, 194, 186, 28, 2, 198, 39,
        69, 139, 242, 24, 167, 16, 81, 29, 200, 207, 99, 255, 47, 13, 88, 206,
        101, 165, 220, 26, 59, 134, 254, 34, 92, 168, 94, 103, 170, 236, 112, 204
    ])
    _FK = [1184304796, 1270900830, 1493524870, 3164752158]
    _CK = [964907, 973793155, 2654690407, 2916866751, 2071233739, 1226140771, 3348805095, 2045549823, 388349611, 800627875, 612403927, 3721562911, 1195432523, 3150178931, 612053223, 2445162591, 67183755, 1174197155, 1393249511, 3331183455, 3822152747, 1332317203, 1804781383, 1990130463, 1282653851, 3376591251, 2910902311, 925872959, 332098219, 735840931, 396665415, 3588844719]

    @staticmethod
    def ROL32(x, n):
        return (x << n) & 0xFFFFFFFF | (x >> (32 - n))

    @staticmethod
    def _BS(X):
        return (SM4._S_BOX[X >> 24 & 255] << 24 | SM4._S_BOX[X >> 16 & 255] << 16 |
                SM4._S_BOX[X >> 8 & 255] << 8 | SM4._S_BOX[X & 255])

    @staticmethod
    def _T0(X):
        X = SM4._BS(X)
        return X ^ SM4.ROL32(X, 2) ^ SM4.ROL32(X, 10) ^ SM4.ROL32(X, 18) ^ SM4.ROL32(X, 24)

    @staticmethod
    def _T1(X):
        X = SM4._BS(X)
        return X ^ SM4.ROL32(X, 13) ^ SM4.ROL32(X, 23)

    @staticmethod
    def _key_expand(key: bytes, rkey: list):
        K0 = int.from_bytes(key[0:4], 'big') ^ SM4._FK[0]
        K1 = int.from_bytes(key[4:8], 'big') ^ SM4._FK[1]
        K2 = int.from_bytes(key[8:12], 'big') ^ SM4._FK[2]
        K3 = int.from_bytes(key[12:16], 'big') ^ SM4._FK[3]
        for i in range(0, 32, 4):
            K0 = K0 ^ SM4._T1(K1 ^ K2 ^ K3 ^ SM4._CK[i]); rkey[i] = K0
            K1 = K1 ^ SM4._T1(K2 ^ K3 ^ K0 ^ SM4._CK[i + 1]); rkey[i + 1] = K1
            K2 = K2 ^ SM4._T1(K3 ^ K0 ^ K1 ^ SM4._CK[i + 2]); rkey[i + 2] = K2
            K3 = K3 ^ SM4._T1(K0 ^ K1 ^ K2 ^ SM4._CK[i + 3]); rkey[i + 3] = K3

    @classmethod
    def key_length(cls):
        return 16

    @classmethod
    def block_length(cls):
        return 16

    def __init__(self, key: bytes):
        if len(key) != self.key_length():
            raise ValueError(f'Key must be {self.key_length()} bytes')
        self._key = key
        self._rkey = [0] * 32
        SM4._key_expand(self._key, self._rkey)
        self._block_buffer = bytearray()
        if not hasattr(SM4, '_T_TABLES'):
            SM4._T_TABLES = SM4._make_t_tables()

    def encrypt(self, block: bytes) -> bytes:
        RK = self._rkey
        X0 = int.from_bytes(block[0:4], 'big')
        X1 = int.from_bytes(block[4:8], 'big')
        X2 = int.from_bytes(block[8:12], 'big')
        X3 = int.from_bytes(block[12:16], 'big')
        for i in range(0, 32, 4):
            X0 = X0 ^ SM4._T0(X1 ^ X2 ^ X3 ^ RK[i])
            X1 = X1 ^ SM4._T0(X2 ^ X3 ^ X0 ^ RK[i + 1])
            X2 = X2 ^ SM4._T0(X3 ^ X0 ^ X1 ^ RK[i + 2])
            X3 = X3 ^ SM4._T0(X0 ^ X1 ^ X2 ^ RK[i + 3])
        B = self._block_buffer; B.clear()
        B.extend(X3.to_bytes(4, 'big')); B.extend(X2.to_bytes(4, 'big'))
        B.extend(X1.to_bytes(4, 'big')); B.extend(X0.to_bytes(4, 'big'))
        return bytes(B)

    def decrypt(self, block: bytes) -> bytes:
        RK = self._rkey
        X0 = int.from_bytes(block[0:4], 'big')
        X1 = int.from_bytes(block[4:8], 'big')
        X2 = int.from_bytes(block[8:12], 'big')
        X3 = int.from_bytes(block[12:16], 'big')
        for i in range(0, 32, 4):
            X0 = X0 ^ SM4._T0(X1 ^ X2 ^ X3 ^ RK[31 - i])
            X1 = X1 ^ SM4._T0(X2 ^ X3 ^ X0 ^ RK[30 - i])
            X2 = X2 ^ SM4._T0(X3 ^ X0 ^ X1 ^ RK[29 - i])
            X3 = X3 ^ SM4._T0(X0 ^ X1 ^ X2 ^ RK[28 - i])
        B = self._block_buffer; B.clear()
        B.extend(X3.to_bytes(4, 'big')); B.extend(X2.to_bytes(4, 'big'))
        B.extend(X1.to_bytes(4, 'big')); B.extend(X0.to_bytes(4, 'big'))
        return bytes(B)

    @classmethod
    def _make_t_tables(cls):
        S = cls._S_BOX
        def rol(x, n): return (x << n) & 0xFFFFFFFF | (x >> (32 - n))
        def L(y): return y ^ rol(y, 2) ^ rol(y, 10) ^ rol(y, 18) ^ rol(y, 24)
        T0 = [0] * 256; T1 = [0] * 256; T2 = [0] * 256; T3 = [0] * 256
        for i in range(256):
            s = S[i]
            T0[i] = L(s << 24); T1[i] = L(s << 16); T2[i] = L(s << 8); T3[i] = L(s)
        return (T0, T1, T2, T3)

    def _bulk(self, data: bytes, rk) -> bytes:
        n = len(data)
        out = bytearray(n)
        T0, T1, T2, T3 = self._T_TABLES
        unpack_from = struct.unpack_from
        pack_into = struct.pack_into
        idx = 0
        while idx < n:
            X0, X1, X2, X3 = unpack_from('>IIII', data, idx)
            for i in range(0, 32, 4):
                t = X1 ^ X2 ^ X3 ^ rk[i]
                X0 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
                t = X2 ^ X3 ^ X0 ^ rk[i + 1]
                X1 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
                t = X3 ^ X0 ^ X1 ^ rk[i + 2]
                X2 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
                t = X0 ^ X1 ^ X2 ^ rk[i + 3]
                X3 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
            pack_into('>IIII', out, idx, X3, X2, X1, X0)
            idx += 16
        return bytes(out)

    def encrypt_bulk(self, data: bytes) -> bytes:
        lib = _load_fast_sm4()
        if lib is not None:
            data = bytes(data); n = len(data)
            inbuf = ctypes.create_string_buffer(data)
            outbuf = ctypes.create_string_buffer(n)
            lib.sm4_ecb(ctypes.create_string_buffer(self._key), inbuf, outbuf, n, 1)
            return outbuf.raw
        return self._bulk(data, self._rkey)

    def decrypt_bulk(self, data: bytes) -> bytes:
        lib = _load_fast_sm4()
        if lib is not None:
            data = bytes(data); n = len(data)
            inbuf = ctypes.create_string_buffer(data)
            outbuf = ctypes.create_string_buffer(n)
            lib.sm4_ecb(ctypes.create_string_buffer(self._key), inbuf, outbuf, n, 0)
            return outbuf.raw
        return self._bulk(data, self._rkey[::-1])


_FAST_SM4_LIB = None
_FAST_SM4_TRIED = False


def _sm4_c_source() -> str:
    sbox = SM4._S_BOX; fk = SM4._FK; ck = SM4._CK
    L = []
    L.append('// auto-generated fast SM4 from tool.py')
    L.append('#include <stdint.h>')
    L.append('#include <stddef.h>')
    L.append('')
    L.append('static const uint8_t SBOX[256] = { ' + ', '.join(str(x) for x in sbox) + ' };')
    L.append('static const uint32_t FK[4] = { ' + ', '.join(hex(x) for x in fk) + ' };')
    L.append('static const uint32_t CK[32] = { ' + ', '.join(hex(x) for x in ck) + ' };')
    L.append('')
    L.append('static inline uint32_t rotl(uint32_t x, int n){ return (x << n) | (x >> (32 - n)); }')
    L.append('static inline uint32_t load_be(const uint8_t* p){ return ((uint32_t)p[0]<<24)|((uint32_t)p[1]<<16)|((uint32_t)p[2]<<8)|(uint32_t)p[3]; }')
    L.append('static inline void store_be(uint8_t* p, uint32_t v){ p[0]=(uint8_t)(v>>24); p[1]=(uint8_t)(v>>16); p[2]=(uint8_t)(v>>8); p[3]=(uint8_t)v; }')
    L.append('static inline uint32_t sb(uint32_t x){ return ((uint32_t)SBOX[(x>>24)&0xff]<<24)|((uint32_t)SBOX[(x>>16)&0xff]<<16)|((uint32_t)SBOX[(x>>8)&0xff]<<8)|(uint32_t)SBOX[x&0xff]; }')
    L.append('static inline uint32_t t0(uint32_t x){ x = sb(x); return x ^ rotl(x,2) ^ rotl(x,10) ^ rotl(x,18) ^ rotl(x,24); }')
    L.append('static inline uint32_t t1(uint32_t x){ x = sb(x); return x ^ rotl(x,13) ^ rotl(x,23); }')
    L.append('')
    L.append('static void expand(const uint8_t* key, uint32_t rk[32]){')
    L.append('    uint32_t k0 = load_be(key) ^ FK[0];')
    L.append('    uint32_t k1 = load_be(key+4) ^ FK[1];')
    L.append('    uint32_t k2 = load_be(key+8) ^ FK[2];')
    L.append('    uint32_t k3 = load_be(key+12) ^ FK[3];')
    L.append('    for (int i = 0; i < 32; i++){')
    L.append('        k0 ^= t1(k1 ^ k2 ^ k3 ^ CK[i]); rk[i] = k0;')
    L.append('        k1 ^= t1(k2 ^ k3 ^ k0 ^ CK[++i]); rk[i] = k1;')
    L.append('        k2 ^= t1(k3 ^ k0 ^ k1 ^ CK[++i]); rk[i] = k2;')
    L.append('        k3 ^= t1(k0 ^ k1 ^ k2 ^ CK[++i]); rk[i] = k3;')
    L.append('    }')
    L.append('}')
    L.append('')
    L.append('static void crypt_block(const uint8_t* in, uint8_t* out, const uint32_t* rk){')
    L.append('    uint32_t x0 = load_be(in), x1 = load_be(in+4), x2 = load_be(in+8), x3 = load_be(in+12);')
    L.append('    for (int i = 0; i < 32; i += 4){')
    L.append('        x0 ^= t0(x1 ^ x2 ^ x3 ^ rk[i]);')
    L.append('        x1 ^= t0(x2 ^ x3 ^ x0 ^ rk[i+1]);')
    L.append('        x2 ^= t0(x3 ^ x0 ^ x1 ^ rk[i+2]);')
    L.append('        x3 ^= t0(x0 ^ x1 ^ x2 ^ rk[i+3]);')
    L.append('    }')
    L.append('    store_be(out, x3); store_be(out+4, x2); store_be(out+8, x1); store_be(out+12, x0);')
    L.append('}')
    L.append('')
    L.append('void sm4_ecb(const uint8_t* key, const uint8_t* in, uint8_t* out, size_t len, int encrypt){')
    L.append('    uint32_t rk[32]; expand(key, rk);')
    L.append('    if (!encrypt){ for (int i = 0; i < 16; i++){ uint32_t tmp = rk[i]; rk[i] = rk[31-i]; rk[31-i] = tmp; } }')
    L.append('    for (size_t off = 0; off < len; off += 16){ crypt_block(in + off, out + off, rk); }')
    L.append('}')
    return '\n'.join(L)


def _load_fast_sm4():
    global _FAST_SM4_LIB, _FAST_SM4_TRIED
    if _FAST_SM4_TRIED:
        return _FAST_SM4_LIB
    _FAST_SM4_TRIED = True
    try:
        tool_dir = Path(__file__).resolve().parent
        src_path = tool_dir / 'sm4_fast.c'
        so_path = tool_dir / 'sm4_fast.so'
        c_src = _sm4_c_source()
        if not src_path.exists():
            src_path.write_text(c_src)
        if src_path.read_text() != c_src:
            src_path.write_text(c_src)
        recompile = (not so_path.exists()) or (so_path.stat().st_mtime < src_path.stat().st_mtime)
        if recompile:
            for cc in ('gcc', 'cc', 'clang'):
                try:
                    r = subprocess.run([cc, '-O2', '-shared', '-fPIC', str(src_path), '-o', str(so_path)],
                                       capture_output=True, timeout=120)
                    if r.returncode == 0 and so_path.exists():
                        break
                except Exception:
                    continue
        if not so_path.exists():
            return None
        lib = ctypes.CDLL(str(so_path))
        lib.sm4_ecb.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p, ctypes.c_size_t, ctypes.c_int]
        lib.sm4_ecb.restype = None
        _FAST_SM4_LIB = lib
        return lib
    except Exception:
        return None


class Misc:
    @staticmethod
    def pad_to_n(data: bytes, n: int) -> bytes:
        padding = n - len(data) % n
        if padding == n:
            return data
        return data + b'\x00' * padding

    @staticmethod
    def align_up(x: int, n: int) -> int:
        return (x + n - 1) // n * n


class Reader:
    def __init__(self, buffer, cursor=0):
        self._buffer = buffer
        self._cursor = cursor

    def u1(self, move_cursor=True) -> int:
        return self.unpack('B', move_cursor=move_cursor)[0]
    def u4(self, move_cursor=True) -> int:
        return self.unpack('<I', move_cursor=move_cursor)[0]
    def u8(self, move_cursor=True) -> int:
        return self.unpack('<Q', move_cursor=move_cursor)[0]
    def i1(self, move_cursor=True) -> int:
        return self.unpack('b', move_cursor=move_cursor)[0]
    def i4(self, move_cursor=True) -> int:
        return self.unpack('<i', move_cursor=move_cursor)[0]
    def i8(self, move_cursor=True) -> int:
        return self.unpack('<q', move_cursor=move_cursor)[0]
    def s(self, n: int, move_cursor=True) -> bytes:
        return self.unpack(f'{n}s', move_cursor=move_cursor)[0]

    def unpack(self, f: str, offset=0, move_cursor=True):
        x = struct.unpack_from(f, self._buffer, self._cursor + offset)
        if move_cursor:
            self._cursor += struct.calcsize(f)
        return x

    def string(self, move_cursor=True) -> str:
        length = self.i4(move_cursor=move_cursor)
        if length == 0:
            return str()
        assert length > 0
        offset = 0 if move_cursor else 4
        return self.unpack(f'{length}s', offset=offset, move_cursor=move_cursor)[0].rstrip(b'\x00').decode()


class PakInfo:
    def __init__(self, buffer, keystream: List[int]):
        def decrypt_index_encrypted(x):
            return (x ^ keystream[3]) & 255
        def decrypt_magic(x):
            return x ^ keystream[2]
        def decrypt_index_hash(x):
            key = struct.pack('<5I', *keystream[4:][:5])
            return bytes((a ^ b for a, b in zip(x, key)))
        def decrypt_index_size(x):
            return x ^ (keystream[10] << 32 | keystream[11])
        def decrypt_index_offset(x):
            return x ^ (keystream[0] << 32 | keystream[1])
        reader = Reader(buffer[-PakInfo._mem_size((-1)):])
        self.index_encrypted = decrypt_index_encrypted(reader.u1()) == 1
        self.magic = decrypt_magic(reader.u4())
        self.version = reader.u4()
        self.index_hash = decrypt_index_hash(reader.s(20)) if self.version >= 6 else bytes()
        self.index_size = decrypt_index_size(reader.u8())
        self.index_offset = decrypt_index_offset(reader.u8())
        if self.version <= 3:
            self.index_encrypted = False

    @staticmethod
    def _mem_size(_: int) -> int:
        return 45


class TencentPakInfo(PakInfo):
    def __init__(self, buffer, keystream: List[int]):
        def decrypt_unk(x):
            key = struct.pack('<8I', *keystream[7:][:8])
            return bytes((a ^ b for a, b in zip(x, key)))
        def decrypt_stem_hash(x):
            return x ^ keystream[8]
        def decrypt_unk_hash(x):
            return x ^ keystream[9]
        super().__init__(buffer, keystream)
        reader = Reader(buffer[-TencentPakInfo._mem_size(self.version):])
        self.unk1 = decrypt_unk(reader.s(32)) if self.version >= 7 else bytes()
        self.packed_key = reader.s(256) if self.version >= 8 else bytes()
        self.packed_iv = reader.s(256) if self.version >= 8 else bytes()
        self.packed_index_hash = reader.s(256) if self.version >= 8 else bytes()
        self.stem_hash = decrypt_stem_hash(reader.u4()) if self.version >= 9 else 0
        self.unk2 = decrypt_unk_hash(reader.u4()) if self.version >= 9 else 0
        self.content_org_hash = reader.s(20) if self.version >= 12 else bytes()

    @staticmethod
    def _mem_size(version: int) -> int:
        size_for_7 = 32 if version >= 7 else 0
        size_for_8 = 768 if version >= 8 else 0
        size_for_9 = 8 if version >= 9 else 0
        size_for_12 = 20 if version >= 12 else 0
        return PakInfo._mem_size(version) + size_for_7 + size_for_8 + size_for_9 + size_for_12


class PakCompressedBlock:
    def __init__(self, reader: Reader):
        self.start = reader.u8()
        self.end = reader.u8()


@dataclass
class TencentPakEntry:
    def __init__(self, reader: Reader, version: int):
        self.content_hash = reader.s(20)
        if version <= 1:
            _ = reader.u8()
        self.offset = reader.u8()
        self.uncompressed_size = reader.u8()
        self.compression_method = reader.u4() & CM_MASK
        self.size = reader.u8()
        self.unk1 = reader.u1() if version >= 5 else 0
        self.unk2 = reader.s(20) if version >= 5 else bytes()
        if self.compression_method != 0 and version >= 3:
            self.compressed_blocks = [PakCompressedBlock(reader) for _ in range(reader.u4())]
        else:
            self.compressed_blocks = []
        self.compression_block_size = reader.u4() if version >= 4 else 0
        self.encrypted = reader.u1() == 1 if version >= 4 else False
        self.encryption_method = reader.u4() if version >= 12 else 0
        self.index_new_sep = reader.u4() if version >= 12 else 0


class PakCrypto:
    class _LCG:
        def __init__(self, seed: int):
            self.state = seed
        def next(self) -> int:
            MASK_32 = 4294967295
            MSB_1 = 2147483648
            def wrap(x):
                x &= MASK_32
                if not x & MSB_1:
                    return x
                return (x + MSB_1 & MASK_32) - MSB_1
            x1 = wrap(1103515245 * self.state)
            self.state = wrap(x1 + 12345)
            x2 = wrap(x1 + 77880) if self.state < 0 else self.state
            return (x2 >> 16 & MASK_32) % 32767

    @staticmethod
    def zuc_keystream() -> List[int]:
        zuc = gmalg.ZUC(ZUC_KEY, ZUC_IV)
        return [struct.unpack('>I', zuc.generate())[0] for _ in range(16)]

    @staticmethod
    def _xorxor(buffer, x):
        return bytes((buffer[i] ^ x[i % len(x)] for i in range(len(buffer))))

    @staticmethod
    def _hashhash(buffer, n):
        result = bytes()
        for i in range(math.ceil(n / SHA1.digest_size)):
            result += SHA1.new(buffer).digest()
        if len(result) >= n:
            return result[:n]
        result += b'\x00' * (n - len(result))
        return result

    @staticmethod
    def _meowmeow(buffer):
        def unpad(x):
            skip = 1 + next((i for i in range(len(x)) if x[i] != 0))
            return x[skip:]
        if len(buffer) < 43:
            return bytes()
        x1 = buffer[1:][:SHA1.digest_size]
        x2 = buffer[SHA1.digest_size + 1:]
        x1 = PakCrypto._xorxor(x1, PakCrypto._hashhash(x2, len(x1)))
        x2 = PakCrypto._xorxor(x2, PakCrypto._hashhash(x1, len(x2)))
        part1, m = (x2[:SHA1.digest_size], x2[SHA1.digest_size:])
        if part1 != SHA1.new(b'\x00' * SHA1.digest_size).digest():
            return bytes()
        return unpad(m)

    @staticmethod
    def rsa_extract(signature, modulus):
        c = int.from_bytes(signature, 'little')
        n = int.from_bytes(modulus, 'little')
        e = 65537
        m = pow(c, e, n).to_bytes(256, 'little').rstrip(b'\x00')
        return PakCrypto._meowmeow(Misc.pad_to_n(m, 4))

    @staticmethod
    def _decrypt_simple1(ciphertext):
        return bytes((x ^ SIMPLE1_DECRYPT_KEY for x in ciphertext))

    @staticmethod
    def _decrypt_simple2(ciphertext):
        class RollingKey:
            def __init__(self, initial_value):
                self._value = initial_value
            def update(self, x):
                self._value ^= x
                return self._value
        assert len(ciphertext) % SIMPLE2_BLOCK_SIZE == 0
        initial_key, = struct.unpack('<I', SIMPLE2_DECRYPT_KEY)
        rolling_key = RollingKey(initial_key)
        plaintext = (struct.pack('<I', rolling_key.update(x)) for x in struct.unpack(f'<{len(ciphertext) // 4}I', ciphertext))
        return bytes(it.chain.from_iterable(plaintext))

    @staticmethod
    @lru_cache(maxsize=1)
    def _derive_sm4_key(file_path: PurePath, encryption_method: int) -> bytes:
        part1 = file_path.stem.lower()
        if encryption_method == EM_SM4_2:
            secret = SM4_SECRET_2
        else:
            if encryption_method == EM_SM4_4:
                secret = SM4_SECRET_4
            else:
                index = (encryption_method - EM_SM4_NEW_BASE) % len(SM4_SECRET_NEW)
                secret = f'{SM4_SECRET_NEW[index]}{encryption_method}'
        return SHA1.new(str(part1 + secret).encode()).digest()[:SM4.key_length()]

    @staticmethod
    @lru_cache(maxsize=1)
    def _sm4_context_for_key(key: bytes) -> SM4:
        return SM4(key)

    @staticmethod
    def _decrypt_sm4(ciphertext, file_path, encryption_method):
        assert len(ciphertext) % SM4.block_length() == 0
        key = PakCrypto._derive_sm4_key(file_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        return sm4.decrypt_bulk(ciphertext)

    @staticmethod
    def decrypt_index(ciphertext, pak_info):
        if pak_info.version > 7:
            key = PakCrypto.rsa_extract(pak_info.packed_key, RSA_MOD_1)
            iv = PakCrypto.rsa_extract(pak_info.packed_iv, RSA_MOD_1)
            assert len(key) == 32 and len(iv) == 32
            aes = AES.new(key, MODE_CBC, iv[:16])
            return unpad(aes.decrypt(ciphertext), AES.block_size)
        return bytes(PakCrypto._decrypt_simple1(ciphertext))

    @staticmethod
    def _is_simple1_method(m): return m == EM_SIMPLE1
    @staticmethod
    def _is_simple2_method(m): return m == EM_SIMPLE2 or m == 17
    @staticmethod
    def _is_sm4_method(m): return m == EM_SM4_2 or m == EM_SM4_4 or m & EM_SM4_NEW_MASK != 0

    @staticmethod
    def align_encrypted_content_size(n, encryption_method):
        if PakCrypto._is_simple2_method(encryption_method):
            return Misc.align_up(n, SIMPLE2_BLOCK_SIZE)
        if PakCrypto._is_sm4_method(encryption_method):
            return Misc.align_up(n, SM4.block_length())
        return n

    @staticmethod
    def decrypt_block(ciphertext, file, encryption_method):
        if PakCrypto._is_simple1_method(encryption_method):
            return PakCrypto._decrypt_simple1(ciphertext)
        if PakCrypto._is_simple2_method(encryption_method):
            return PakCrypto._decrypt_simple2(ciphertext)
        if PakCrypto._is_sm4_method(encryption_method):
            return PakCrypto._decrypt_sm4(ciphertext, file, encryption_method)
        raise ValueError(f'Unknown encryption method: {encryption_method}')

    @staticmethod
    @lru_cache(maxsize=33)
    def generate_block_indices(n: int, encryption_method: int) -> List[int]:
        if not PakCrypto._is_sm4_method(encryption_method):
            return list(range(n))
        permutation = []
        lcg = PakCrypto._LCG(n)
        while len(permutation) != n:
            x = lcg.next() % n
            if x not in permutation:
                permutation.append(x)
        inverse = [0] * len(permutation)
        for i, x in enumerate(permutation):
            inverse[x] = i
        return inverse


class PakCompression:
    @staticmethod
    @lru_cache(maxsize=33)
    def _zstd_decompressor(dict: ZstdCompressionDict) -> ZstdDecompressor:
        return ZstdDecompressor(dict)

    @staticmethod
    def zstd_dictionary(dict_data) -> ZstdCompressionDict:
        return ZstdCompressionDict(dict_data, DICT_TYPE_AUTO)

    @staticmethod
    def decompress_block(block, dict, compression_method):
        if compression_method == CM_ZLIB:
            try:
                return zlib.decompress(block)
            except zlib.error:
                return block
        if compression_method == CM_ZSTD or compression_method == CM_ZSTD_DICT:
            if compression_method != CM_ZSTD_DICT:
                dict = None
            return PakCompression._zstd_decompressor(dict).decompress(block)
        raise ValueError(f'Unknown compression method: {compression_method}')


class TencentPakFile:
    def __init__(self, file_path: PurePath, is_od=False):
        self._file_path = file_path
        with open(file_path, 'rb') as file:
            self._file_content = memoryview(file.read())
        self._is_od = is_od
        self._mount_point = PurePath()
        self._is_zstd_with_dict = 'zsdic' in str(self._file_path)
        self._zstd_dict = None
        self._zstd_dict_entry = None
        self._files = []
        self._index = {}
        self._pak_info = TencentPakInfo(self._file_content, PakCrypto.zuc_keystream())
        self._verify_stem_hash()
        self._tencent_load_index()

    def _verify_stem_hash(self):
        if not self._is_od and self._pak_info.version >= 9:
            try:
                assert self._pak_info.stem_hash == zlib.crc32(self._file_path.stem.encode('utf-32le'))
            except AssertionError:
                console.print(f"[bold bright_yellow]⚠️  Warning:[/] [bold white]pak filename differs from original stem.[/]")

    def _tencent_load_index(self):
        index_data = self._file_content[self._pak_info.index_offset:][:self._pak_info.index_size]
        if self._pak_info.index_encrypted:
            index_data = PakCrypto.decrypt_index(index_data, self._pak_info)
        self._verify_index_hash(index_data)
        self._load_index(index_data)

    def _verify_index_hash(self, index_data):
        expected_hash = self._pak_info.index_hash
        if not self._is_od and self._pak_info.version >= 8:
            if expected_hash != PakCrypto.rsa_extract(self._pak_info.packed_index_hash, RSA_MOD_2):
                pass
        assert expected_hash == SHA1.new(index_data).digest()

    @staticmethod
    def _construct_mount_point(mount_point):
        result = PurePath()
        for part in PurePath(mount_point).parts:
            if part != '..':
                result /= part
        return result

    def _peek_content(self, offset, size, encryption_method):
        size = PakCrypto.align_encrypted_content_size(size, encryption_method)
        return self._file_content[offset:][:size]

    def _peek_block_content(self, block, encryption_method):
        size = PakCrypto.align_encrypted_content_size(block.end - block.start, encryption_method)
        return self._file_content[block.start:][:size]

    def _construct_zstd_dict(self, dict_entry):
        assert not self._zstd_dict
        assert not dict_entry.encrypted
        assert dict_entry.compression_method == CM_NONE
        reader = Reader(self._peek_content(dict_entry.offset, dict_entry.size, 0))
        dict_size = reader.u8()
        _ = reader.u4()
        assert dict_size == reader.u4()
        dict_data = reader.s(dict_size)
        self._zstd_dict = PakCompression.zstd_dictionary(dict_data)

    def _load_index(self, index_data):
        if self._pak_info.version <= 10:
            raise ValueError(f'Unsupported version: {self._pak_info.version}')
        reader = Reader(index_data)
        self._mount_point = self._construct_mount_point(reader.string())
        self._files = [TencentPakEntry(reader, self._pak_info.version) for _ in range(reader.u4())]
        for _ in range(reader.u8()):
            dir_path = PurePath(reader.string())
            e = {reader.string(): self._files[~reader.i4()] for _ in range(reader.u8())}
            if self._is_zstd_with_dict and dir_path.name == 'zstddic':
                assert len(e) == 1
                self._zstd_dict_entry = e[[*e.keys()][0]]
                self._construct_zstd_dict(self._zstd_dict_entry)
            else:
                self._index.update({PurePath(dir_path): e})

    def _write_to_disk(self, file_path, entry):
        encryption_method = entry.encryption_method
        compression_method = entry.compression_method
        with open(file_path, 'wb') as file:
            if compression_method == CM_NONE:
                data = self._peek_content(entry.offset, entry.size, encryption_method)
                if entry.encrypted:
                    data = PakCrypto.decrypt_block(data, file_path, encryption_method)
                file.write(data[:entry.uncompressed_size])
                return
            try:
                for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), encryption_method):
                    data = self._peek_block_content(entry.compressed_blocks[x], encryption_method)
                    if entry.encrypted:
                        data = PakCrypto.decrypt_block(data, file_path, encryption_method)
                    data = PakCompression.decompress_block(data, self._zstd_dict, compression_method)
                    file.write(data)
            except Exception:
                file.seek(0); file.truncate()
                raw = bytearray()
                for blk in entry.compressed_blocks:
                    raw += self._peek_block_content(blk, encryption_method)
                file.write(raw)

    def dump(self, out_path):
        out_path = out_path / self._mount_point
        out_path.mkdir(parents=True, exist_ok=True)
        total_files = sum(len(d) for d in self._index.values())
        with Progress(
            SpinnerColumn(),
            TextColumn("[bold bright_cyan][UNPACK][/] {task.description}"),
            BarColumn(),
            TaskProgressColumn(),
            TimeElapsedColumn(),
            console=console
        ) as progress:
            task = progress.add_task("Extracting...", total=total_files)
            for dir_path, dir_content in self._index.items():
                current_out_path = out_path / dir_path
                current_out_path.mkdir(parents=True, exist_ok=True)
                for file_name, entry in dir_content.items():
                    self._write_to_disk(current_out_path / file_name, entry)
                    progress.update(task, advance=1)


# ═══════════════════════════════════════════════════════════════
# REPACK FUNCTIONS
# ═══════════════════════════════════════════════════════════════

def dump_unpacking_log(pak_file, output_log_path: Path):
    with open(output_log_path, 'w', encoding='utf-8') as log_file:
        log_file.write('=' * 80 + '\n')
        log_file.write('NDX ENGINE V6.0 — PAK UNPACKING LOG\n')
        log_file.write('@NDXCHEATS\n')
        log_file.write('=' * 80 + '\n\n')
        log_file.write(f'PAK File: {pak_file._file_path}\n')
        log_file.write(f'PAK Info Version: {pak_file._pak_info.version}\n')
        log_file.write(f'Mount Point: {pak_file._mount_point}\n')
        log_file.write('-' * 80 + '\n\n')
        file_count = 0
        for dir_path, files in pak_file._index.items():
            for file_name, entry in files.items():
                file_count += 1
                full_path = str(PurePath(dir_path) / file_name).replace('\\', '/')
                log_file.write(f'\n[{file_count}] {full_path}\n')
                log_file.write(f'  Uncompressed Size: {entry.uncompressed_size:,} bytes\n')
                log_file.write(f'  Compressed Size: {entry.size:,} bytes\n')
                log_file.write(f'  Compression Method: {entry.compression_method}\n')
                log_file.write(f'  Encryption Method: {entry.encryption_method}\n')
                log_file.write(f'  Compressed Blocks: {len(entry.compressed_blocks)}\n')
        log_file.write('\n' + '=' * 80 + '\n')
        log_file.write('END OF LOG\n')
        log_file.write('=' * 80 + '\n')
    console.print(f'[bold bright_green]✓ Debug log saved: {output_log_path}[/bold bright_green]')


def _encrypt_plaintext(plaintext: bytes, pak_relative_path: PurePath, encryption_method: int) -> bytes:
    if PakCrypto._is_simple1_method(encryption_method):
        return bytes((b ^ SIMPLE1_DECRYPT_KEY for b in plaintext))
    if PakCrypto._is_simple2_method(encryption_method):
        pad = -len(plaintext) % SIMPLE2_BLOCK_SIZE
        plaintext += b'\x00' * pad
        key, = struct.unpack('<I', SIMPLE2_DECRYPT_KEY)
        rolling = key
        out = []
        for x, in struct.iter_unpack('<I', plaintext):
            c = rolling ^ x
            out.append(c)
            rolling ^= c
        return struct.pack(f'<{len(out)}I', *out)
    if PakCrypto._is_sm4_method(encryption_method):
        key = PakCrypto._derive_sm4_key(pak_relative_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        pad_len = -len(plaintext) % 16
        if pad_len > 0:
            plaintext = plaintext + b'\x00' * pad_len
        return sm4.encrypt_bulk(plaintext)
    return plaintext


def _repack_uncompressed(outfh, pak_file, entry, pak_relative_path, new_data):
    enc_method = entry.encryption_method
    target_size = entry.size
    enc_region = PakCrypto.align_encrypted_content_size(target_size, enc_method) if entry.encrypted else target_size
    plaintext = new_data[:enc_region]
    if entry.encrypted:
        a = PakCrypto.align_encrypted_content_size(len(plaintext), enc_method)
        plaintext += b'\x00' * (a - len(plaintext))
        cipher = _encrypt_plaintext(plaintext, pak_relative_path, enc_method)
        outfh.seek(entry.offset)
        outfh.write(cipher)
        with open(pak_file._file_path, 'rb') as src:
            src.seek(entry.offset + len(cipher))
            outfh.write(src.read(enc_region - len(cipher)))
    else:
        outfh.seek(entry.offset)
        outfh.write(plaintext)
        with open(pak_file._file_path, 'rb') as src:
            src.seek(entry.offset + len(plaintext))
            outfh.write(src.read(target_size - len(plaintext)))


def _best_compress(chunk, cm, zstd_dict=None, fast=False):
    if cm == CM_ZLIB:
        return zlib.compress(chunk, 1 if fast else 9)
    if cm in (CM_ZSTD, CM_ZSTD_DICT):
        zd = zstd_dict if cm == CM_ZSTD_DICT else None
        levels = [6, 3, 1] if fast else [22, 19, 16, 13, 10, 7, 4, 1]
        for lvl in levels:
            try:
                return ZstdCompressor(level=lvl, dict_data=zd, threads=1).compress(chunk)
            except Exception:
                continue
    return chunk


def _pw_string(s):
    if not s: return struct.pack('<i', 0)
    b = s.encode('utf-8') + b'\x00'
    return struct.pack('<i', len(b)) + b


def _pw_entry(e, v):
    w = bytearray(e.content_hash)
    w += struct.pack('<Q', e.offset)
    w += struct.pack('<Q', e.uncompressed_size)
    w += struct.pack('<I', e.compression_method)
    w += struct.pack('<Q', e.size)
    if v >= 5:
        w += bytes([e.unk1])
        w += e.unk2
    if e.compression_method != CM_NONE and v >= 3:
        w += struct.pack('<I', len(e.compressed_blocks))
        for b in e.compressed_blocks:
            w += struct.pack('<QQ', b.start, b.end)
    if v >= 4:
        w += struct.pack('<I', e.compression_block_size)
        w += bytes([1 if e.encrypted else 0])
    if v >= 12:
        w += struct.pack('<II', e.encryption_method, e.index_new_sep)
    return bytes(w)


def _get_all_dirs_and_mp(pak_file):
    raw = bytes(pak_file._file_content[
        pak_file._pak_info.index_offset:][:pak_file._pak_info.index_size])
    if pak_file._pak_info.index_encrypted:
        raw = PakCrypto.decrypt_index(raw, pak_file._pak_info)
    r = Reader(raw)
    mp = r.string()
    num_files = r.u4()
    for _ in range(num_files):
        TencentPakEntry(r, pak_file._pak_info.version)
    dirs = {}
    for _ in range(r.u8()):
        dp = r.string()
        cnt = r.u8()
        dirs[dp] = {r.string(): pak_file._files[~r.i4()] for _ in range(cnt)}
    return mp, dirs


def _normalize_dir_key(path_str):
    s = str(path_str).replace('\\', '/').strip('/')
    return (s + '/') if s else ''


def _find_existing_dir(all_dirs, want_dir):
    want = _normalize_dir_key(want_dir).strip('/').lower()
    if not want:
        return ''
    for k in all_dirs:
        if k.strip('/').lower() == want:
            return k
    best = None
    for k in all_dirs:
        key = k.strip('/').lower()
        if key and want.endswith('/' + key):
            if best is None or len(key) > len(best):
                best = k
    return best


def _strip_mount_prefix(pak_file, rel_dir):
    mp = str(pak_file._mount_point).replace('\\', '/').strip('/')
    rd = str(rel_dir).replace('\\', '/').strip('/')
    if mp and (rd.lower() == mp.lower() or rd.lower().startswith(mp.lower() + '/')):
        return rd[len(mp):].lstrip('/')
    return rd


def _pick_template(pak_file, all_dirs, target_dir, file_name):
    ext = Path(file_name).suffix.lower()
    if target_dir in all_dirs:
        for name, e in all_dirs[target_dir].items():
            if Path(name).suffix.lower() == ext:
                return e
    for dp, files in all_dirs.items():
        for name, e in files.items():
            if Path(name).suffix.lower() == ext:
                return e
    for dp, files in all_dirs.items():
        for name, e in files.items():
            return e
    return pak_file._files[0] if pak_file._files else None


def _default_compression(pak_file):
    cm_counter = {}
    for e in pak_file._files:
        cm = e.compression_method
        if cm in (CM_ZLIB, CM_ZSTD, CM_ZSTD_DICT):
            cm_counter[cm] = cm_counter.get(cm, 0) + 1
    if pak_file._is_zstd_with_dict and cm_counter.get(CM_ZSTD_DICT, 0):
        return CM_ZSTD_DICT
    if cm_counter.get(CM_ZSTD, 0):
        return CM_ZSTD
    if cm_counter.get(CM_ZSTD_DICT, 0):
        return CM_ZSTD
    return CM_ZLIB


def _write_entry_content(out_buf, ne, plaintext, pak_rel, zstd_dict, fast=False):
    if ne.compression_method == CM_NONE:
        cipher = (_encrypt_plaintext(plaintext, pak_rel, ne.encryption_method)
                  if ne.encrypted else plaintext)
        ne.offset = len(out_buf)
        ne.size = len(plaintext)
        ne.uncompressed_size = len(plaintext)
        out_buf += cipher
        return
    cs = ne.compression_block_size if ne.compression_block_size > 0 else 65536
    chunks = [plaintext[i:i + cs] for i in range(0, len(plaintext), cs)]
    if not chunks:
        ne.compressed_blocks = []
        ne.offset = len(out_buf)
        ne.size = 0
        ne.uncompressed_size = 0
        return
    n = len(chunks)
    inv = PakCrypto.generate_block_indices(n, ne.encryption_method) if ne.encrypted else list(range(n))
    file_order = [0] * n
    for j in range(n):
        file_order[inv[j]] = j
    new_blks = [None] * n
    for k in range(n):
        chunk = chunks[file_order[k]]
        compressed = _best_compress(chunk, ne.compression_method, zstd_dict, fast=fast)
        cipher = (_encrypt_plaintext(compressed, pak_rel, ne.encryption_method)
                  if ne.encrypted else compressed)
        blk = PakCompressedBlock.__new__(PakCompressedBlock)
        blk.start = len(out_buf)
        blk.end = blk.start + len(cipher)
        out_buf += cipher
        new_blks[k] = blk
    ne.compressed_blocks = new_blks
    ne.offset = new_blks[0].start
    ne.size = sum(b.end - b.start for b in new_blks)
    ne.uncompressed_size = len(plaintext)


def _extract_entry_plaintext(pak_file, entry, full_path):
    em = entry.encryption_method
    cm = entry.compression_method
    path = PurePath(full_path)
    if cm == CM_NONE:
        data = pak_file._peek_content(entry.offset, entry.size, em)
        if entry.encrypted:
            data = PakCrypto.decrypt_block(data, path, em)
        return bytes(data[:entry.uncompressed_size])
    out = bytearray()
    for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), em):
        data = pak_file._peek_block_content(entry.compressed_blocks[x], em)
        if entry.encrypted:
            data = PakCrypto.decrypt_block(data, path, em)
        out += PakCompression.decompress_block(data, pak_file._zstd_dict, cm)
    return bytes(out)


def _copy_original_content(out_buf, pak_file, ne, old_entry):
    em = old_entry.encryption_method
    if old_entry.compression_method == CM_NONE:
        read_sz = (PakCrypto.align_encrypted_content_size(old_entry.size, em)
                   if old_entry.encrypted else old_entry.size)
        ne.offset = len(out_buf)
        out_buf += bytes(pak_file._file_content[old_entry.offset: old_entry.offset + read_sz])
    elif old_entry.compressed_blocks:
        new_blks = []
        for ob in old_entry.compressed_blocks:
            unc = ob.end - ob.start
            enc = (PakCrypto.align_encrypted_content_size(unc, em)
                   if old_entry.encrypted else unc)
            nb = PakCompressedBlock.__new__(PakCompressedBlock)
            nb.start = len(out_buf)
            nb.end = nb.start + unc
            out_buf += bytes(pak_file._file_content[ob.start: ob.start + enc])
            new_blks.append(nb)
        ne.compressed_blocks = new_blks
        ne.offset = new_blks[0].start
    ne.encryption_method = old_entry.encryption_method
    ne.encrypted = old_entry.encrypted


def _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path):
    version = pak_file._pak_info.version
    keystream = PakCrypto.zuc_keystream()
    eidx = {id(new_files[i]): i for i in range(len(new_files))}
    old_id_to_new_idx = {id(pak_file._files[i]): i for i in range(len(pak_file._files))}
    idx = bytearray(_pw_string(mp_str))
    idx += struct.pack('<I', len(new_files))
    for ne in new_files:
        idx += _pw_entry(ne, version)
    idx += struct.pack('<Q', len(all_dirs))
    for dp_str, dir_files in all_dirs.items():
        idx += _pw_string(dp_str)
        idx += struct.pack('<Q', len(dir_files))
        for name, old_e in dir_files.items():
            idx += _pw_string(name)
            found_idx = eidx.get(id(old_e))
            if found_idx is None:
                found_idx = old_id_to_new_idx.get(id(old_e))
            if found_idx is None:
                copy_of = next((k for k, v in old_to_new.items() if v is old_e), None)
                if copy_of is not None:
                    found_idx = eidx.get(id(old_to_new[copy_of]))
            if found_idx is None:
                for i, e in enumerate(new_files):
                    if e.offset == old_e.offset and e.size == old_e.size:
                        found_idx = i
                        break
            idx += struct.pack('<i', ~found_idx if found_idx is not None else -1)
    index_plain = bytes(idx)
    new_sha1 = SHA1.new(index_plain).digest()
    if pak_file._pak_info.index_encrypted:
        key = PakCrypto.rsa_extract(pak_file._pak_info.packed_key, RSA_MOD_1)
        iv = PakCrypto.rsa_extract(pak_file._pak_info.packed_iv, RSA_MOD_1)
        aes = AES.new(key, MODE_CBC, iv[:16])
        pad = (-len(index_plain)) % AES.block_size or AES.block_size
        index_bytes = aes.encrypt(index_plain + bytes([pad] * pad))
    else:
        index_bytes = index_plain
    new_idx_offset = len(out_buf)
    new_idx_size = len(index_bytes)
    out_buf += index_bytes
    footer_sz = TencentPakInfo._mem_size(version)
    new_footer = bytearray(pak_file._file_content[-footer_sz:])
    h_key = struct.pack('<5I', *keystream[4:9])
    new_footer[-36:-16] = bytes(a ^ b for a, b in zip(new_sha1, h_key))
    new_footer[-16:-8] = ((new_idx_size ^ (keystream[10] << 32 | keystream[11])).to_bytes(8, 'little'))
    new_footer[-8:] = ((new_idx_offset ^ (keystream[0] << 32 | keystream[1])).to_bytes(8, 'little'))
    out_buf += new_footer
    with open(output_path, 'wb') as f:
        f.write(out_buf)


def repack_pak_file_full(pak_file, edited_root, output_path, target_path=None, force_add=False):
    import copy as _cp
    console.print(f'[bold bright_cyan]📦 Full PAK Rebuild mode[/bold bright_cyan]')
    if target_path:
        console.print(f'[bold bright_cyan]🎯 Target path: {target_path}[/bold bright_cyan]')
    edit_files = []
    for p in Path(edited_root).rglob('*'):
        if p.is_file():
            edit_files.append(p)
    if not edit_files:
        console.print('[bold bright_red]❌ No files found in EDIT folder![/bold bright_red]')
        return 0
    console.print(f'[bold bright_cyan]📁 Found {len(edit_files)} files[/bold bright_cyan]')
    version = pak_file._pak_info.version
    keystream = PakCrypto.zuc_keystream()
    orig_fc = pak_file._file_content
    mp_str, all_dirs = _get_all_dirs_and_mp(pak_file)
    if target_path and force_add:
        target_path = target_path.replace('\\', '/')
        matched_dir = None
        for existing_dir in all_dirs.keys():
            if existing_dir.strip('/').lower() == target_path.strip('/').lower():
                matched_dir = existing_dir
                break
        if matched_dir:
            target_path = matched_dir
        else:
            target_path = target_path.strip('/') + '/'
    pak_name_map = {}
    for dir_path, files in pak_file._index.items():
        for name, entry in files.items():
            full_path = str(PurePath(dir_path) / name).replace('\\', '/')
            pak_name_map.setdefault(name.lower(), []).append((full_path, entry))
    edited = {}
    for p in edit_files:
        fl = p.name.lower()
        found_match = False
        if fl in pak_name_map:
            cands = pak_name_map[fl]
            if target_path:
                target_candidates = [(fp, e) for fp, e in cands if target_path.strip('/') in fp]
                if target_candidates:
                    sz = p.stat().st_size
                    sm = [(fp, e) for fp, e in target_candidates if e.uncompressed_size == sz]
                    fp, ent = sm[0] if sm else target_candidates[0]
                    edited[fp] = (p, ent)
                    found_match = True
            if not found_match:
                sz = p.stat().st_size
                sm = [(fp, e) for fp, e in cands if e.uncompressed_size == sz]
                fp, ent = sm[0] if sm else cands[0]
                if target_path:
                    new_fp = f"{target_path.rstrip('/')}/{p.name}"
                    edited[new_fp] = (p, ent)
                else:
                    edited[fp] = (p, ent)
                found_match = True
        if not found_match:
            stem = p.stem.lower()
            ext = p.suffix.lower()
            for dir_path, files in pak_file._index.items():
                for name, entry in files.items():
                    if Path(name).stem.lower() == stem and Path(name).suffix.lower() == ext:
                        full_path = str(PurePath(dir_path) / name).replace('\\', '/')
                        if target_path:
                            new_fp = f"{target_path.rstrip('/')}/{p.name}"
                            edited[new_fp] = (p, entry)
                        else:
                            edited[full_path] = (p, entry)
                        found_match = True
                        break
                if found_match:
                    break
        if not found_match and force_add and target_path:
            template_entry = None
            for dir_path, files in pak_file._index.items():
                for name, entry in files.items():
                    if Path(name).suffix.lower() == p.suffix.lower():
                        template_entry = entry
                        break
                if template_entry:
                    break
            if not template_entry:
                for dir_path, files in pak_file._index.items():
                    for name, entry in files.items():
                        template_entry = entry
                        break
                    if template_entry:
                        break
            if template_entry:
                new_fp = f"{target_path.rstrip('/')}/{p.name}"
                edited[new_fp] = (p, template_entry)
    if not edited:
        console.print('[bold bright_red]❌ No files to repack![/bold bright_red]')
        return 0
    console.print(f'  [bold bright_cyan]📁 Files to repack: {len(edited)}[/bold bright_cyan]')
    new_files = []
    for e in pak_file._files:
        ne = _cp.copy(e)
        ne.compressed_blocks = [_cp.copy(b) for b in e.compressed_blocks]
        new_files.append(ne)
    old_to_new = {id(pak_file._files[i]): new_files[i] for i in range(len(pak_file._files))}
    edited_paths = {fp: p for fp, (p, _) in edited.items()}
    out_buf = bytearray()
    for dp_str, dir_files in list(all_dirs.items()):
        for name, old_entry in list(dir_files.items()):
            full_path = str(PurePath(dp_str) / name).replace('\\', '/')
            ne = old_to_new.get(id(old_entry), None)
            if ne is None:
                ne = _cp.copy(old_entry)
                ne.compressed_blocks = [_cp.copy(b) for b in old_entry.compressed_blocks]
                new_files.append(ne)
                old_to_new[id(old_entry)] = ne
            em = old_entry.encryption_method
            cm = old_entry.compression_method
            if full_path in edited_paths:
                p, template = edited[full_path]
                new_raw = p.read_bytes()
                pak_rel = PurePath(full_path)
                ne.content_hash = SHA1.new(new_raw).digest()
                ne.uncompressed_size = len(new_raw)
                ne.compression_method = template.compression_method if template else cm
                ne.encryption_method = template.encryption_method if template else em
                ne.encrypted = template.encrypted if template else old_entry.encrypted
                ne.unk1 = template.unk1 if template else old_entry.unk1
                if template and target_path:
                    full_path_str = mp_str + full_path
                    ne.unk2 = SHA1.new(full_path_str.lower().encode('utf-8')).digest()
                else:
                    ne.unk2 = template.unk2 if template else old_entry.unk2
                ne.index_new_sep = template.index_new_sep if template else old_entry.index_new_sep
                if ne.compression_method == CM_NONE:
                    cipher = (_encrypt_plaintext(new_raw, pak_rel, ne.encryption_method)
                              if ne.encrypted else new_raw)
                    ne.offset = len(out_buf)
                    ne.size = len(new_raw)
                    ne.uncompressed_size = len(new_raw)
                    out_buf += cipher
                else:
                    cs = (template.compression_block_size if template and template.compression_block_size > 0
                          else old_entry.compression_block_size if old_entry.compression_block_size > 0
                          else 65536)
                    chunks = [new_raw[i:i + cs] for i in range(0, len(new_raw), cs)]
                    new_blks = []
                    for chunk in chunks:
                        compressed = _best_compress(chunk, ne.compression_method, pak_file._zstd_dict)
                        cipher = (_encrypt_plaintext(compressed, pak_rel, ne.encryption_method)
                                  if ne.encrypted else compressed)
                        blk = PakCompressedBlock.__new__(PakCompressedBlock)
                        blk.start = len(out_buf)
                        blk.end = blk.start + len(cipher)
                        out_buf += cipher
                        new_blks.append(blk)
                    ne.compressed_blocks = new_blks
                    ne.offset = new_blks[0].start if new_blks else len(out_buf)
                    ne.size = sum(b.end - b.start for b in new_blks)
                    ne.uncompressed_size = len(new_raw)
                console.print(f'[bold bright_green]✓ Processed: {full_path}[/bold bright_green]')
            else:
                if cm == CM_NONE:
                    read_sz = (PakCrypto.align_encrypted_content_size(old_entry.size, em)
                               if old_entry.encrypted else old_entry.size)
                    ne.offset = len(out_buf)
                    out_buf += bytes(orig_fc[old_entry.offset: old_entry.offset + read_sz])
                elif old_entry.compressed_blocks:
                    new_blks = []
                    for ob in old_entry.compressed_blocks:
                        unc = ob.end - ob.start
                        enc = (PakCrypto.align_encrypted_content_size(unc, em)
                               if old_entry.encrypted else unc)
                        nb = PakCompressedBlock.__new__(PakCompressedBlock)
                        nb.start = len(out_buf)
                        nb.end = nb.start + unc
                        out_buf += bytes(orig_fc[ob.start: ob.start + enc])
                        new_blks.append(nb)
                    ne.compressed_blocks = new_blks
                    ne.offset = new_blks[0].start
    if target_path and force_add:
        for fp, (p, template) in edited.items():
            already_processed = False
            for dp_str, dir_files in all_dirs.items():
                for name, entry in dir_files.items():
                    if str(PurePath(dp_str) / name).replace('\\', '/') == fp:
                        already_processed = True
                        break
                if already_processed:
                    break
            if not already_processed:
                ne = _cp.copy(template)
                new_raw = p.read_bytes()
                pak_rel = PurePath(fp)
                ne.content_hash = SHA1.new(new_raw).digest()
                ne.uncompressed_size = len(new_raw)
                ne.compression_method = template.compression_method
                ne.encryption_method = template.encryption_method
                ne.encrypted = template.encrypted
                ne.unk1 = template.unk1
                full_path_str = mp_str + fp
                ne.unk2 = SHA1.new(full_path_str.lower().encode('utf-8')).digest()
                ne.index_new_sep = template.index_new_sep
                if ne.compression_method == CM_NONE:
                    cipher = (_encrypt_plaintext(new_raw, pak_rel, ne.encryption_method)
                              if ne.encrypted else new_raw)
                    ne.offset = len(out_buf)
                    ne.size = len(new_raw)
                    ne.uncompressed_size = len(new_raw)
                    out_buf += cipher
                else:
                    cs = template.compression_block_size if template.compression_block_size > 0 else 65536
                    chunks = [new_raw[i:i + cs] for i in range(0, len(new_raw), cs)]
                    new_blks = []
                    for chunk in chunks:
                        compressed = _best_compress(chunk, ne.compression_method, pak_file._zstd_dict)
                        cipher = (_encrypt_plaintext(compressed, pak_rel, ne.encryption_method)
                                  if ne.encrypted else compressed)
                        blk = PakCompressedBlock.__new__(PakCompressedBlock)
                        blk.start = len(out_buf)
                        blk.end = blk.start + len(cipher)
                        out_buf += cipher
                        new_blks.append(blk)
                    ne.compressed_blocks = new_blks
                    ne.offset = new_blks[0].start if new_blks else len(out_buf)
                    ne.size = sum(b.end - b.start for b in new_blks)
                    ne.uncompressed_size = len(new_raw)
                new_files.append(ne)
                if target_path not in all_dirs:
                    all_dirs[target_path] = {}
                all_dirs[target_path][p.name] = ne
                console.print(f'[bold bright_green]✓ Added new: {fp}[/bold bright_green]')
    _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path)
    return len(edited)


def inject_edit_files(pak_file, edit_root, output_path, protect_new=False, sm4_type=47):
    import copy as _cp
    version = pak_file._pak_info.version
    if version < 12:
        raise ValueError(f'Unsupported pak version: {version} (need >= 12)')
    edit_files = [p for p in Path(edit_root).rglob('*') if p.is_file()]
    if not edit_files:
        raise ValueError(f'No files found in EDIT folder: {edit_root}')
    mp_str, all_dirs = _get_all_dirs_and_mp(pak_file)
    injections = {}
    for p in edit_files:
        rel = p.relative_to(edit_root)
        parts = rel.parts
        file_name = parts[-1]
        rel_dir = '/'.join(parts[:-1]).replace('\\', '/')
        rel_dir = _strip_mount_prefix(pak_file, rel_dir)
        target_dir = _find_existing_dir(all_dirs, rel_dir) if rel_dir.strip('/') else ''
        if target_dir is None:
            target_dir = _normalize_dir_key(rel_dir)
        existing = None
        if target_dir in all_dirs:
            for name, e in list(all_dirs[target_dir].items()):
                if name.lower() == file_name.lower():
                    existing = (name, e)
                    break
        if existing:
            full_path = target_dir + existing[0]
            injections[full_path] = (p, existing[1], False)
        else:
            full_path = target_dir + file_name
            template = _pick_template(pak_file, all_dirs, target_dir, file_name)
            injections[full_path] = (p, template, True)
        console.print(f'  [bold bright_green]◈[/] [bold bright_white]{full_path}[/bold bright_white] '
                      f'[bold bright_yellow]({"replace" if existing else "add new"})[/]')
    new_files = []
    for e in pak_file._files:
        ne = _cp.copy(e)
        ne.compressed_blocks = [_cp.copy(b) for b in e.compressed_blocks]
        new_files.append(ne)
    old_to_new = {id(pak_file._files[i]): new_files[i] for i in range(len(pak_file._files))}
    out_buf = bytearray()
    edited_count = 0
    new_count = 0
    for dp_str, dir_files in list(all_dirs.items()):
        for name, old_entry in list(dir_files.items()):
            full_path = str(PurePath(dp_str) / name).replace('\\', '/')
            ne = old_to_new.get(id(old_entry), None)
            if ne is None:
                ne = _cp.copy(old_entry)
                ne.compressed_blocks = [_cp.copy(b) for b in old_entry.compressed_blocks]
                new_files.append(ne)
                old_to_new[id(old_entry)] = ne
            if full_path in injections:
                p, template, is_new = injections[full_path]
                new_raw = p.read_bytes()
                pak_rel = PurePath(full_path)
                ne.content_hash = SHA1.new(new_raw).digest()
                ne.uncompressed_size = len(new_raw)
                if is_new:
                    ne.compression_method = _default_compression(pak_file)
                    if protect_new:
                        ne.encryption_method = sm4_type
                        ne.encrypted = True
                    else:
                        ne.encryption_method = template.encryption_method if template else 0
                        ne.encrypted = template.encrypted if template else False
                    ne.unk1 = template.unk1 if template else 0
                    ne.compression_block_size = (template.compression_block_size if template
                                                 and template.compression_block_size > 0 else 65536)
                    ne.index_new_sep = template.index_new_sep if template else 0
                    new_count += 1
                else:
                    ne.compression_method = old_entry.compression_method
                    if protect_new:
                        ne.encryption_method = sm4_type
                        ne.encrypted = True
                    else:
                        ne.encryption_method = old_entry.encryption_method
                        ne.encrypted = old_entry.encrypted
                    ne.unk1 = old_entry.unk1
                    ne.compression_block_size = (old_entry.compression_block_size
                                                 if old_entry.compression_block_size > 0 else 65536)
                    ne.index_new_sep = old_entry.index_new_sep
                    edited_count += 1
                ne.unk2 = SHA1.new((mp_str + full_path).lower().encode('utf-8')).digest()
                _write_entry_content(out_buf, ne, new_raw, pak_rel, pak_file._zstd_dict)
                console.print(f'  [bold bright_green]✓[/] '
                              f'[bold bright_green]{"Edited" if not is_new else "Added"}[/]: {full_path} '
                              f'[bold bright_yellow]({len(new_raw):,} bytes)[/]')
            else:
                _copy_original_content(out_buf, pak_file, ne, old_entry)
    for full_path, (p, template, is_new) in injections.items():
        if not is_new:
            continue
        already = False
        for dp_str, dir_files in all_dirs.items():
            for name, entry in dir_files.items():
                if str(PurePath(dp_str) / name).replace('\\', '/') == full_path:
                    already = True
                    break
            if already:
                break
        if already:
            continue
        ne = _cp.copy(template) if template else None
        if ne is None:
            ne = TencentPakEntry(Reader(b''), version)
            ne.compression_method = CM_NONE
            ne.encrypted = False
        else:
            ne.compressed_blocks = [_cp.copy(b) for b in template.compressed_blocks]
        new_raw = p.read_bytes()
        pak_rel = PurePath(full_path)
        ne.content_hash = SHA1.new(new_raw).digest()
        ne.uncompressed_size = len(new_raw)
        ne.compression_method = _default_compression(pak_file)
        if protect_new:
            ne.encryption_method = sm4_type
            ne.encrypted = True
        else:
            ne.encryption_method = template.encryption_method if template else 0
            ne.encrypted = template.encrypted if template else False
        ne.unk1 = template.unk1 if template else 0
        ne.compression_block_size = (template.compression_block_size if template
                                     and template.compression_block_size > 0 else 65536)
        ne.index_new_sep = template.index_new_sep if template else 0
        ne.unk2 = SHA1.new((mp_str + full_path).lower().encode('utf-8')).digest()
        _write_entry_content(out_buf, ne, new_raw, pak_rel, pak_file._zstd_dict)
        new_files.append(ne)
        old_to_new[id(ne)] = ne
        dp_key = full_path.rsplit('/', 1)[0] + '/' if '/' in full_path else ''
        all_dirs.setdefault(dp_key, {})[full_path.rsplit('/', 1)[-1]] = ne
        new_count += 1
        console.print(f'  [bold bright_green]✓[/] [bold bright_green]Added[/]: {full_path} '
                      f'[bold bright_yellow]({len(new_raw):,} bytes)[/]')
    _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path)
    return edited_count, new_count


def protect_pak_file(pak_file, output_path, sm4_type=47):
    import copy as _cp
    version = pak_file._pak_info.version
    if version < 12:
        raise ValueError(f'Unsupported pak version: {version} (need >= 12)')
    mp_str, all_dirs = _get_all_dirs_and_mp(pak_file)
    new_files = []
    for e in pak_file._files:
        ne = _cp.copy(e)
        ne.compressed_blocks = [_cp.copy(b) for b in e.compressed_blocks]
        new_files.append(ne)
    old_to_new = {id(pak_file._files[i]): new_files[i] for i in range(len(pak_file._files))}
    out_buf = bytearray()
    protected = 0
    skipped = 0
    for dp_str, dir_files in list(all_dirs.items()):
        for name, old_entry in list(dir_files.items()):
            full_path = str(PurePath(dp_str) / name).replace('\\', '/')
            ne = old_to_new.get(id(old_entry), None)
            if ne is None:
                ne = _cp.copy(old_entry)
                ne.compressed_blocks = [_cp.copy(b) for b in old_entry.compressed_blocks]
                new_files.append(ne)
                old_to_new[id(old_entry)] = ne
            is_marker = (old_entry.compression_method == CM_NONE and old_entry.size == 0)
            is_zdict = (pak_file._zstd_dict_entry is not None and old_entry is pak_file._zstd_dict_entry)
            if is_marker or is_zdict:
                _copy_original_content(out_buf, pak_file, ne, old_entry)
                skipped += 1
                continue
            try:
                plaintext = _extract_entry_plaintext(pak_file, old_entry, full_path)
            except Exception:
                _copy_original_content(out_buf, pak_file, ne, old_entry)
                skipped += 1
                console.print(f"  [bold bright_red]![/] [bold bright_red]Skipped: {full_path}[/]")
                continue
            ne.compression_method = old_entry.compression_method
            if ne.compression_method == CM_NONE:
                ne.compression_method = CM_ZLIB
            ne.encryption_method = sm4_type
            ne.encrypted = True
            ne.unk1 = old_entry.unk1
            ne.unk2 = old_entry.unk2
            ne.index_new_sep = old_entry.index_new_sep
            ne.compression_block_size = (old_entry.compression_block_size
                                         if old_entry.compression_block_size > 0 else 65536)
            _write_entry_content(out_buf, ne, plaintext, PurePath(full_path), pak_file._zstd_dict, fast=True)
            protected += 1
    _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path)
    return protected, skipped


# ═══════════════════════════════════════════════════════════════
# FILE SELECTOR
# ═══════════════════════════════════════════════════════════════

def display_file_selector(title, folder_path, file_pattern="*.pak"):
    files = [p for p in folder_path.glob(file_pattern) if p.is_file()]
    if not files:
        console.print(f"[bold bright_red][ERROR] No {file_pattern} files in {folder_path}[/]")
        return None, None
    selection_table = Table(title=f"[bold bright_cyan]{title}[/]", expand=True, box=ROUNDED, border_style="bold bright_yellow")
    selection_table.add_column("[bold bright_yellow]#[/]", justify="center", style="bold bright_yellow", width=4)
    selection_table.add_column("[bold bright_green]File Name[/]", justify="left", style="bold bright_green")
    selection_table.add_column("[bold bright_magenta]Size[/]", justify="right", style="bold bright_magenta")
    for i, f in enumerate(files, 1):
        size_mb = f.stat().st_size / (1024 * 1024)
        selection_table.add_row(str(i), f.name, f"{size_mb:.2f} MB")
    console.print(selection_table)
    try:
        idx = int(console.input(f"\n[bold bright_yellow]Select file number (1-{len(files)}): [/]")) - 1
        if idx < 0 or idx >= len(files):
            console.print("[bold bright_red][ERROR] Invalid selection[/]")
            return None, None
        return files[idx], files
    except ValueError:
        console.print("[bold bright_red][ERROR] Please enter a valid number[/]")
        return None, None


# ═══════════════════════════════════════════════════════════════
# DIRECTORY SETUP
# ═══════════════════════════════════════════════════════════════

def ensure_directories(base_dir: Path):
    (base_dir / "PAK").mkdir(parents=True, exist_ok=True)
    (base_dir / "UNPACK").mkdir(parents=True, exist_ok=True)
    (base_dir / "REPACK").mkdir(parents=True, exist_ok=True)
    (base_dir / "RESULT").mkdir(parents=True, exist_ok=True)
    pak_tool_dir = base_dir / "PAK TOOL"
    (pak_tool_dir / "EDIT").mkdir(parents=True, exist_ok=True)
    (pak_tool_dir / "UNPACK").mkdir(parents=True, exist_ok=True)
    (pak_tool_dir / "RESULT").mkdir(parents=True, exist_ok=True)
    (pak_tool_dir / "PAK").mkdir(parents=True, exist_ok=True)


# ═══════════════════════════════════════════════════════════════
# UI — BANNER + MENU
# ═══════════════════════════════════════════════════════════════

def _print_responsive_banner():
    _load_ui_theme()
    w = _term_width()
    c = [_tc(i) for i in range(6)]

    if w < 45:
        console.print()
        console.print(Align.center(Text("╔══════════════════════════╗", style=f"bold {c[0]}")))
        console.print(Align.center(Text("║  NDX ENGINE  //  V6.0   ║", style=f"bold {c[1]}")))
        console.print(Align.center(Text("║  DARK HACKER TERMINAL   ║", style=f"bold {c[2]}")))
        console.print(Align.center(Text("╚══════════════════════════╝", style=f"bold {c[0]}")))
        console.print(Align.center(Text("[ ACCESS GRANTED ]", style=f"bold {c[3]}")))
        console.print()
        return

    console.print()
    console.print(Align.center(Text("╭──────────────────────────────────────────────────────╮", style=f"bold {c[0]}")))
    console.print(Align.center(Text("│  ███╗   ██╗██████╗ ██╗  ██╗    ███████╗███╗   ██╗  │", style=f"bold {c[1]}")))
    console.print(Align.center(Text("│  ████╗  ██║██╔══██╗╚██╗██╔╝    ██╔════╝████╗  ██║  │", style=f"bold {c[0]}")))
    console.print(Align.center(Text("│  ██╔██╗ ██║██║  ██║ ╚███╔╝     █████╗  ██╔██╗ ██║  │", style=f"bold {c[4]}")))
    console.print(Align.center(Text("│  ██║╚██╗██║██║  ██║ ██╔██╗     ██╔══╝  ██║╚██╗██║  │", style=f"bold {c[1]}")))
    console.print(Align.center(Text("│  ██║ ╚████║██████╔╝██╔╝ ██╗    ███████╗██║ ╚████║  │", style=f"bold {c[0]}")))
    console.print(Align.center(Text("│  ╚═╝  ╚═══╝╚═════╝ ╚═╝  ╚═╝    ╚══════╝╚═╝  ╚═══╝  │", style=f"bold {c[2]}")))
    console.print(Align.center(Text("├──────────────────────────────────────────────────────┤", style=f"bold {c[3]}")))
    console.print(Align.center(Text("│        NDX ENGINE V6.0  •  @NDXCHEATS              │", style=f"bold {c[4]}")))
    console.print(Align.center(Text("│        UNPACK • REPACK • INJECT • PROTECT           │", style=f"bold {c[2]}")))
    console.print(Align.center(Text("╰──────────────────────────────────────────────────────╯", style=f"bold {c[0]}")))
    console.print()


# ═══════════════════════════════════════════════════════════════
# 200+ COLORFUL UI THEMES / CUSTOM COLORS
# ═══════════════════════════════════════════════════════════════

UI_THEME_FILE = ".ndx_hacker_ui_theme.json"

# 50 RGB colour presets used by the menu/custom UI.
def _build_ui_themes():
    """50 selectable colour presets. Each preset exposes its RGB value."""
    rgb_colors = [
        ("Matrix Green", (0, 255, 65)), ("Cyber Cyan", (0, 229, 255)),
        ("Hacker Lime", (57, 255, 20)), ("Neon Purple", (139, 0, 255)),
        ("Hot Pink", (255, 0, 170)), ("Laser Blue", (0, 128, 255)),
        ("Electric Blue", (30, 144, 255)), ("Royal Purple", (124, 77, 255)),
        ("Violet", (170, 0, 255)), ("Magenta", (255, 0, 255)),
        ("Red Alert", (255, 23, 68)), ("Crimson", (220, 20, 60)),
        ("Orange", (255, 109, 0)), ("Amber", (255, 176, 0)),
        ("Gold", (255, 215, 0)), ("Yellow", (255, 234, 0)),
        ("Emerald", (0, 200, 83)), ("Toxic Green", (182, 255, 0)),
        ("Mint", (0, 255, 179)), ("Aqua", (0, 255, 255)),
        ("Sky Blue", (0, 191, 255)), ("Deep Blue", (0, 80, 200)),
        ("Indigo", (75, 0, 130)), ("Plasma Pink", (255, 0, 85)),
        ("Neon Rose", (255, 20, 147)), ("Coral", (255, 99, 71)),
        ("Fire Orange", (255, 69, 0)), ("Lava", (255, 45, 0)),
        ("Copper", (184, 115, 51)), ("Lemon", (255, 250, 0)),
        ("Spring", (0, 255, 127)), ("Jade", (0, 168, 107)),
        ("Teal", (0, 128, 128)), ("Turquoise", (64, 224, 208)),
        ("Ice", (175, 238, 238)), ("Steel", (70, 130, 180)),
        ("Midnight Blue", (25, 25, 112)), ("Deep Purple", (48, 0, 80)),
        ("Electric Violet", (145, 0, 255)), ("Fuchsia", (255, 0, 128)),
        ("Bubblegum", (255, 105, 180)), ("Salmon", (250, 128, 114)),
        ("Ruby", (224, 17, 95)), ("Burgundy", (128, 0, 32)),
        ("Dark Orange", (255, 140, 0)), ("Bronze", (205, 127, 50)),
        ("Olive", (128, 128, 0)), ("Forest", (34, 139, 34)),
        ("Dark Cyan", (0, 139, 139)), ("White", (255, 255, 255)),
    ]
    themes = []
    for i, (name, (r, g, b)) in enumerate(rgb_colors, 1):
        # Derive six UI roles from the selected base colour so one click
        # changes the complete interface without asking for six values.
        primary = f"#{r:02X}{g:02X}{b:02X}"
        text = "#F5F7FA"
        success = "#39FF14" if (g >= r and g >= b) else primary
        warning = "#FFD700"
        accent = primary
        secondary = "#00E5FF" if primary != "#00E5FF" else "#8B00FF"
        themes.append({
            "name": f"{name} {i:02d}",
            "rgb": (r, g, b),
            "colors": [primary, accent, success, warning, secondary, text],
        })
    return themes


UI_THEMES = _build_ui_themes()
UI_THEME = {
    "name": "DARK HACKER 01",
    "colors": UI_THEMES[0]["colors"],
    "rgb": UI_THEMES[0]["rgb"],
}


def _ui_theme_path() -> Path:
    if getattr(sys, 'frozen', False):
        base = Path(sys.executable).parent
    else:
        base = Path(__file__).parent
    return base / UI_THEME_FILE


def _load_ui_theme():
    global UI_THEME
    try:
        p = _ui_theme_path()
        if p.exists():
            data = json.loads(p.read_text(encoding="utf-8"))
            colors = data.get("colors")
            if isinstance(colors, list) and len(colors) >= 6:
                UI_THEME = {
                    "name": str(data.get("name", "CUSTOM")),
                    "colors": colors[:6],
                    "rgb": tuple(data.get("rgb", (0, 255, 65)))
                }
    except Exception:
        pass


def _save_ui_theme(theme):
    global UI_THEME
    UI_THEME = {
        "name": theme["name"],
        "colors": list(theme["colors"][:6]),
        "rgb": tuple(theme.get("rgb", (0, 255, 65)))
    }
    try:
        _ui_theme_path().write_text(json.dumps(UI_THEME, indent=2), encoding="utf-8")
    except Exception:
        pass


def _tc(index: int) -> str:
    return UI_THEME["colors"][index % 6]


def _theme_markup(index: int, text: str, bold: bool = True) -> str:
    tag = "bold " if bold else ""
    return f"[{tag}{_tc(index)}]{text}[/]"


def ui_color_customizer(data_path: Path):
    """Select one of exactly 50 RGB colour presets. 51 always means Back."""
    _load_ui_theme()
    while True:
        os.system('cls' if os.name == 'nt' else 'clear')
        c = [_tc(i) for i in range(6)]
        console.print()
        console.print(Align.center(Text("╭────────────── 🎨 NDX COLOR CENTER ──────────────╮", style=f"bold {c[0]}")))
        console.print(Align.center(Text("│        50 RGB COLORS • ONE-CLICK SELECT        │", style=f"bold {c[1]}")))
        console.print(Align.center(Text("╰─────────────────────────────────────────────────╯", style=f"bold {c[3]}")))
        console.print()
        rgb = UI_THEME.get("rgb", (0, 255, 65))
        console.print(f"  {_theme_markup(2, 'CURRENT:')} {_theme_markup(0, UI_THEME['name'])}  {_theme_markup(3, f'RGB{tuple(rgb)}')}")
        console.print()

        # Compact two-column list for Termux. Every number is directly selectable.
        for row in range(25):
            left = UI_THEMES[row]
            right = UI_THEMES[row + 25]
            lr, lg, lb = left["rgb"]
            rr, rg, rb = right["rgb"]
            left_txt = f"{row+1:02d}. {left['name']:<20} RGB({lr:3d},{lg:3d},{lb:3d})"
            right_txt = f"{row+26:02d}. {right['name']:<20} RGB({rr:3d},{rg:3d},{rb:3d})"
            console.print(f"  {_theme_markup(row % 6, left_txt):<46}  {_theme_markup((row+3) % 6, right_txt)}")

        console.print()
        console.print(Align.center(Text("51. ↩ BACK TO MAIN MENU", style=f"bold {c[4]}")))
        console.print()
        choice = safe_input(f"{_theme_markup(0, 'SELECT COLOR (1-50) / BACK (51):')} ").strip()

        if choice == "51":
            return
        try:
            n = int(choice)
        except ValueError:
            console.print(_theme_markup(5, "✗ Enter a number from 1 to 51"))
            time.sleep(0.8)
            continue

        if 1 <= n <= 50:
            selected = UI_THEMES[n - 1]
            _save_ui_theme(selected)
            r, g, b = selected["rgb"]
            console.print()
            console.print(Align.center(Text("✓ COLOR SET SUCCESSFULLY", style=f"bold {_tc(2)}")))
            console.print(Align.center(Text(f"{selected['name']}  •  RGB({r}, {g}, {b})", style=f"bold {_tc(0)}")))
            time.sleep(1.2)
        else:
            console.print(_theme_markup(5, "✗ Invalid number — use 1-50 or 51 for Back"))
            time.sleep(0.8)


_load_ui_theme()


def print_banner():
    os.system('cls' if os.name == 'nt' else 'clear')
    _print_responsive_banner()
    console.print()

    w = _term_width()
    time_str = get_indian_time()

    if w < 45:
        console.print(Align.center(
            Text("🔸 NDX READY", style="bold bright_cyan")
        ))
        console.print(Align.center(
            Text("@NDXCHEATS", style="bold bright_magenta")
        ))
        console.print()
        return

    status = Panel(
        Group(
            Text("", justify="center"),
            Text(f"🔸 {time_str}", style="bold bright_yellow", justify="center"),
            Text("🔸  NDX ENGINE READY  |  Mode: PAK MASTER",
                 style="bold bright_cyan", justify="center"),
            Text("@NDXCHEATS", style="bold bright_magenta", justify="center"),
            Text("", justify="center"),
        ),
        border_style="bold bright_green",
        box=ROUNDED,
        padding=(0, 2),
        width=62,
    )
    console.print(Align.center(status))
    console.print()


def print_enhanced_menu():
    """Dark hacker / cyber-terminal main menu."""
    _load_ui_theme()
    w = _term_width()
    c = [_tc(i) for i in range(6)]
    items = [
        ("01", "UNPACK / REPACK", "📦", "PAK WORKSPACE"),
        ("02", "INJECT / EDIT", "🧩", "MULTI INJECT"),
        ("03", "REPACK TO PATH", "📁", "BUILD OUTPUT"),
        ("04", "PROTECT PAK", "🛡", "SM4 PROTECT"),
        ("05", "DELETE FOLDER", "🗑", "CLEAN WORKSPACE"),
        ("06", "ENCRYPT LUA", "🔒", "LUA ENCRYPTOR"),
        ("07", "UI COLORS", "🎨", "50 RGB COLORS"),
        ("08", "KEY EXPIRY", "⏳", "LIVE FIREBASE"),
        ("09", "EXIT", "⏻", "CLOSE SESSION"),
    ]

    console.print(Align.center(Text("┌─[ MAIN CONTROL ]──────────────────────────────────────┐", style=f"bold {c[0]}")))
    console.print(Align.center(Text("│  STATUS : ONLINE   •   MODE : DARK HACKER            │", style=f"bold {c[2]}")))
    console.print(Align.center(Text("├────────────────────────────────────────────────────────┤", style=f"bold {c[4]}")))

    if w < 55:
        for i, (num, title, icon, desc) in enumerate(items):
            color = c[i % 6]
            console.print(f"  [{c[0]}]│[/] [{color}]{num}[/]  [{color}]{icon} {title:<20}[/] [{c[5]}]{desc}[/]")
        console.print(Align.center(Text("└────────────────────────────────────────────────────────┘", style=f"bold {c[0]}")))
    else:
        for i, (num, title, icon, desc) in enumerate(items):
            color = c[i % 6]
            console.print(
                f"  [{c[0]}]│[/] [{c[3]}]{num}[/]  [{color}]{icon} {title:<22}[/] "
                f"[{c[5]}]» {desc:<18}[/] [{c[0]}]│[/]"
            )
        console.print(Align.center(Text("└────────────────────────────────────────────────────────┘", style=f"bold {c[0]}")))

    console.print()
    console.print(Align.center(Text(f"● THEME: {UI_THEME['name']}   •   SESSION SECURE", style=f"bold {c[2]}")))
    console.print(Align.center(Text("ENTER OPTION >", style=f"bold {c[0]}")))
    console.print()


# ═══════════════════════════════════════════════════════════════
# DELETE FOLDER
# ═══════════════════════════════════════════════════════════════

def delete_folder(data_path: Path):
    folders = []
    for item in data_path.iterdir():
        if item.is_dir() and item.name not in ['PAK', 'UNPACK', 'REPACK', 'RESULT', 'PAK TOOL']:
            folders.append(item)
    if not folders:
        console.print('[bold bright_yellow]⚠️  No folders found to delete![/]')
        return
    folder_table = Table(title="[bold bright_magenta]📁 AVAILABLE FOLDERS[/]",
                         border_style="bold bright_cyan", box=DOUBLE_EDGE)
    folder_table.add_column("#", justify="center", style="bold bright_yellow", width=4)
    folder_table.add_column("Folder Name", justify="left", style="bold bright_green")
    folder_table.add_column("Size", justify="right", style="bold bright_cyan")
    for i, folder in enumerate(folders, 1):
        folder_size = 0
        for root, dirs, files in os.walk(folder):
            for file in files:
                file_path = os.path.join(root, file)
                if os.path.isfile(file_path):
                    folder_size += os.path.getsize(file_path)
        folder_table.add_row(str(i), folder.name, human_size(folder_size))
    console.print(folder_table)
    try:
        choice = int(console.input(f"\n[bold bright_yellow]Select folder number (1-{len(folders)}): [/]"))
        if 1 <= choice <= len(folders):
            selected_folder = folders[choice - 1]
            confirm = safe_input(f"[bold bright_yellow]Delete {selected_folder.name}? (yes/no): [/]").strip().lower()
            if confirm == 'yes':
                shutil.rmtree(selected_folder)
                console.print(f'[bold bright_green]✓ Deleted: {selected_folder.name}[/]')
            else:
                console.print('[bold bright_yellow]⚠️  Cancelled[/]')
        else:
            console.print('[bold bright_red]❌ Invalid selection[/]')
    except ValueError:
        console.print('[bold bright_red]❌ Invalid input[/]')


# ═══════════════════════════════════════════════════════════════
# UNPACK / REPACK SUB-MENU
# ═══════════════════════════════════════════════════════════════

def unpack_repack_menu(data_path):
    while True:
        print_banner()
        console.print()

        console.print("   [bold bright_cyan]╔══════════════════════════════════════════════════╗[/]")
        console.print("   [bold bright_cyan]║[/]  [bold bright_magenta]🔸 UNPACK / REPACK[/]"
                      "                              [bold bright_cyan]║[/]")
        console.print("   [bold bright_cyan]║[/]  [bold bright_yellow]@NDXCHEATS[/]"
                      "                                  [bold bright_cyan]║[/]")
        console.print("   [bold bright_cyan]╠══════════════════════════════════════════════════╣[/]")
        console.print("   [bold bright_cyan]║[/]  [bold bright_yellow]1.[/]  [bold bright_cyan]🔸 UNPACK PAK[/]"
                      "                [bold bright_white]Extract files[/]  [bold bright_cyan]║[/]")
        console.print("   [bold bright_cyan]║[/]  [bold bright_yellow]2.[/]  [bold bright_yellow]🔸 FULL REBUILD[/]"
                      "              [bold bright_white]Rebuild PAK[/]    [bold bright_cyan]║[/]")
        console.print("   [bold bright_cyan]║[/]  [bold bright_yellow]3.[/]  [bold bright_red]🔸 BACK TO MAIN[/]"
                      "           [bold bright_white]Return[/]         [bold bright_cyan]║[/]")
        console.print("   [bold bright_yellow]╚══════════════════════════════════════════════════╝[/]")
        console.print()

        print_decorative_separator("─", "bright_cyan", 50)
        choice = safe_input("ENTER YOUR CHOICE: ")
        print_decorative_separator("─", "bright_cyan", 50)
        console.print()

        if choice == '1':
            pak_dir = data_path / "PAK"
            if not pak_dir.exists():
                console.print(f"[bold bright_red]ERROR: PAK folder not found at {pak_dir}[/]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to UNPACK:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            try:
                console.print(f'[bold bright_cyan]🚀 Unpacking {pak_file.name}...[/]')
                pak = TencentPakFile(pak_file)
                unpack_path = data_path / "UNPACK" / pak_file.stem
                repack_path = data_path / "REPACK" / pak_file.stem
                total_files = sum(len(d) for d in pak._index.values())
                ui = UnpackProgressUI(
                    pak_name=pak_file.name,
                    output_dir=f"UNPACK/{pak_file.stem}",
                    total_files=total_files,
                )
                ui.start()
                for dir_path, dir_content in pak._index.items():
                    current_out_path = unpack_path / pak._mount_point / dir_path
                    current_out_path.mkdir(parents=True, exist_ok=True)
                    for file_name, entry in dir_content.items():
                        full_rel = str(PurePath(dir_path) / file_name).replace('\\', '/')
                        ui.update(full_rel)
                        pak._write_to_disk(current_out_path / file_name, entry)
                ui.stop()
                log_path = unpack_path / f'Debug_{pak_file.stem}.log'
                dump_unpacking_log(pak, log_path)
                for dir_path, _ in pak._index.items():
                    current_repack_path = repack_path / pak._mount_point / dir_path
                    current_repack_path.mkdir(parents=True, exist_ok=True)
                console.print(f'[bold bright_green]✓ SUCCESS: Extracted to {unpack_path}[/]')
            except Exception as e:
                console.print(f'[bold bright_red]❌ Error: {escape(str(e))}[/]')
            safe_input('\nPress Enter to continue...')

        elif choice == '2':
            pak_tool_dir = data_path / "PAK TOOL"
            pak_dir = pak_tool_dir / "PAK"
            edit_dir = pak_tool_dir / "EDIT"
            result_dir = pak_tool_dir / "RESULT"
            if not pak_dir.exists():
                console.print(f"[bold bright_red]ERROR: PAK folder not found at {pak_dir}[/]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to REPACK:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            if not edit_dir.exists() or not any(edit_dir.iterdir()):
                console.print(f'[bold bright_red]❌ ERROR: No files in EDIT folder.[/]')
                console.print('[bold bright_yellow]⚠️  Please place edited files in PAK TOOL/EDIT folder.[/]')
                safe_input('\nPress Enter to continue...')
                continue
            try:
                console.print(f'[bold bright_cyan]🚀 Repacking {pak_file.name}...[/]')
                pak = TencentPakFile(pak_file)
                output_pak = result_dir / pak_file.name
                count = repack_pak_file_full(pak, edit_dir, output_pak)
                if count > 0:
                    console.print(f'[bold bright_green]✓ Repacked {count} files successfully![/]')
                    console.print(f'[bold bright_green]📦 Output: {output_pak}[/]')
                else:
                    console.print('[bold bright_red]❌ No files repacked![/]')
            except Exception as e:
                console.print(f'[bold bright_red]❌ Repack failed:[/] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '3':
            return

        else:
            console.print('[bold bright_red]❌ Invalid choice![/]')
            time.sleep(2)


# ═══════════════════════════════════════════════════════════════
# EXIT SCREEN
# ═══════════════════════════════════════════════════════════════

def _exit_screen(data_path):
    w = _term_width()
    os.system('cls' if os.name == 'nt' else 'clear')
    time_str = get_indian_time()

    if w < 45:
        console.print()
        console.print("[bold bright_cyan]══════════════════════════════[/]")
        console.print(Align.center(Text("🔸 NDX ENGINE V6.0 🔸", style="bold bright_magenta")))
        console.print(Align.center(Text("@NDXCHEATS", style="bold bright_yellow")))
        console.print("[bold bright_cyan]══════════════════════════════[/]")
        console.print()
        console.print(Align.center(Text(f"🔸 {time_str}", style="bold bright_yellow")))
        console.print(Align.center(Text("✓ Session Completed", style="bold bright_green")))
        console.print()
        console.print(Align.center(Text("Thank You!", style="bold bright_white")))
        console.print(Align.center(Text("@NDXCHEATS", style="bold bright_magenta")))
        console.print()
        for i in [3, 2, 1]:
            console.print(Align.center(Text(f"Closing in {i}...", style="bold bright_yellow")))
            time.sleep(0.7)
        return

    console.print()
    console.print(Align.center(
        Text("╭─ 🔸 ─────────────────────────────────────── 🔸 ─╮",
             style="bold bright_cyan")
    ))
    console.print(Align.center(
        Text("│           🔸 NDX ENGINE V6.0 🔸                │",
             style="bold bright_magenta")
    ))
    console.print(Align.center(
        Text("│                @NDXCHEATS                      │",
             style="bold bright_yellow")
    ))
    console.print(Align.center(
        Text("│                                                │", style="bold bright_green")
    ))
    console.print(Align.center(
        Text("│              GOODBYE!                          │",
             style="bold bright_red")
    ))
    console.print(Align.center(
        Text("│                                                │", style="bold bright_green")
    ))
    console.print(Align.center(
        Text("╰─ 🔸 ─────────────────────────────────────── 🔸 ─╯",
             style="bold bright_magenta")
    ))
    console.print()
    console.print(Align.center(
        Text(f"🔸 {time_str}", style="bold bright_yellow")
    ))
    console.print()
    for i in [3, 2, 1]:
        console.print(Align.center(Text(f"⏳ {i}", style="bold bright_red")))
        time.sleep(0.8)
    console.print()
    console.print(Align.center(Text("✓ GOODBYE! 🔸", style="bold bright_green")))
    console.print(Align.center(Text("@NDXCHEATS", style="bold bright_magenta")))
    console.print()
    time.sleep(0.5)


# ═══════════════════════════════════════════════════════════════
# MAIN MENU
# ═══════════════════════════════════════════════════════════════

def main_menu():
    if getattr(sys, 'frozen', False):
        data_path = Path(sys.executable).parent
    else:
        data_path = Path(__file__).parent

    ensure_directories(data_path)

    # 🔸 FIREBASE LOGIN CHECK — हर बार tool शुरू होने पर key मांगी जाएगी
    prompt_login()

    while True:
        print_banner()
        print_enhanced_menu()

        console.print()
        print_decorative_separator("─", "bright_cyan", 50)
        choice = safe_input('ENTER YOUR CHOICE: ')
        print_decorative_separator("─", "bright_cyan", 50)
        console.print()

        if choice == '1':
            unpack_repack_menu(data_path)
            continue

        elif choice == '2':
            pak_tool_dir = data_path / "PAK TOOL"
            pak_dir = pak_tool_dir / "PAK"
            edit_dir = pak_tool_dir / "EDIT"
            result_dir = pak_tool_dir / "RESULT"
            if not pak_dir.exists():
                console.print(f"[bold bright_red]ERROR: PAK folder not found at {pak_dir}[/]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to INJECT INTO:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            if not edit_dir.exists() or not any(edit_dir.iterdir()):
                console.print(f'[bold bright_red]❌ ERROR: No files in PAK TOOL/EDIT folder.[/]')
                console.print('[bold bright_yellow]⚠️  Place each file at its in-pak path.[/]')
                safe_input('\nPress Enter to continue...')
                continue
            console.print()
            console.print('[bold bright_yellow]🔒 Encrypt the injected files with SM4?[/]')
            console.print('[bold white]YES = game-native encryption (recommended, no plaintext).[/]')
            enc_choice = safe_input('[bold bright_cyan]Encrypt injected files? (Y/n): [/]').strip().lower()
            protect_new = enc_choice not in ('n', 'no')
            try:
                console.print(f'[bold bright_cyan]🚀 Injecting files into {pak_file.name}...[/]')
                pak = TencentPakFile(pak_file)
                output_pak = result_dir / pak_file.name
                edited, added = inject_edit_files(pak, edit_dir, output_pak, protect_new=protect_new, sm4_type=47)
                console.print()
                console.print(f'[bold bright_green]✓ Edited: {edited} files | Added: {added} files[/]')
                console.print(f'[bold bright_green]📦 Output: {output_pak}[/]')
                console.print('[bold bright_green]🎮 PAK is GAME READY![/]')
            except Exception as e:
                console.print(f'[bold bright_red]❌ Inject failed:[/] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '3':
            pak_tool_dir = data_path / "PAK TOOL"
            pak_dir = pak_tool_dir / "PAK"
            edit_dir = pak_tool_dir / "EDIT"
            result_dir = pak_tool_dir / "RESULT"
            if not pak_dir.exists():
                console.print(f"[bold bright_red]ERROR: PAK folder not found at {pak_dir}[/]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to REPACK TO PATH:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            if not edit_dir.exists() or not any(edit_dir.iterdir()):
                console.print(f'[bold bright_red]❌ ERROR: No files in EDIT folder.[/]')
                safe_input('\nPress Enter to continue...')
                continue
            console.print()
            console.print('[bold bright_yellow]📂 Enter the target path inside the PAK:[/]')
            console.print('[bold white]Example: Content/Lua/GameLua/Mod/BRMod/Gameplay/Core[/]')
            target_path = safe_input('[bold bright_cyan]Path: [/]').strip()
            if not target_path:
                console.print('[bold bright_red]❌ No path provided![/]')
                safe_input('\nPress Enter to continue...')
                continue
            target_path = target_path.replace('\\', '/').strip('/')
            try:
                console.print(f'[bold bright_cyan]🚀 Adding files to {target_path} in {pak_file.name}...[/]')
                pak = TencentPakFile(pak_file)
                output_pak = result_dir / pak_file.name
                count = repack_pak_file_full(pak, edit_dir, output_pak, target_path, force_add=True)
                if count > 0:
                    console.print()
                    console.print(f'[bold bright_green]✓ Successfully processed {count} files to {target_path}![/]')
                    console.print(f'[bold bright_green]📦 Output: {output_pak}[/]')
                    console.print('[bold bright_green]🎮 PAK is now GAME READY![/]')
                else:
                    console.print('[bold bright_red]❌ No files were processed![/]')
            except Exception as e:
                console.print(f'[bold bright_red]❌ Repack failed:[/] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '4':
            pak_tool_dir = data_path / "PAK TOOL"
            pak_dir = pak_tool_dir / "PAK"
            result_dir = pak_tool_dir / "RESULT"
            if not pak_dir.exists():
                console.print(f"[bold bright_red]ERROR: PAK TOOL/PAK folder not found at {pak_dir}[/]")
                safe_input('\nPress Enter to continue...')
                continue
            pak_file, _ = display_file_selector("📁 Available .pak files to PROTECT:", pak_dir)
            if not pak_file:
                safe_input('\nPress Enter to continue...')
                continue
            console.print()
            console.print('[bold bright_magenta]🔒 PROTECT MODE[/]')
            console.print('[bold white]Re-encrypts EVERY file with game-native SM4 encryption.[/]')
            console.print('[bold white]Generic unpackers will NOT be able to read the pak content.[/]')
            console.print('[bold bright_yellow]Output keeps the SAME filename so the game still finds it.[/]')
            confirm = safe_input('[bold bright_magenta]Start PROTECT? (yes/no): [/]').strip().lower()
            if confirm not in ('y', 'yes'):
                console.print('[bold bright_yellow]Cancelled.[/]')
                safe_input('\nPress Enter to continue...')
                continue
            try:
                console.print(f'[bold bright_magenta]🔒 Protecting {pak_file.name}...[/]')
                pak = TencentPakFile(pak_file)
                output_pak = result_dir / pak_file.name
                protected, skipped = protect_pak_file(pak, output_pak, sm4_type=47)
                console.print()
                console.print(f'[bold bright_green]✓ PROTECTED: {protected} files re-encrypted (SM4)[/]')
                console.print(f'[bold bright_yellow]Skipped: {skipped} files[/]')
                console.print(f'[bold bright_green]📦 Output: {output_pak}[/]')
                console.print('[bold bright_green]🎮 Game-ready + protected![/]')
            except Exception as e:
                console.print(f'[bold bright_red]❌ Protect failed:[/] {e}')
                import traceback
                traceback.print_exc()
            safe_input('\nPress Enter to continue...')

        elif choice == '5':
            delete_folder(data_path)
            safe_input('\nPress Enter to continue...')

        elif choice == '6':
            file_encrypt_decrypt_menu(data_path)
            continue

        elif choice == '7':
            ui_color_customizer(data_path)
            continue

        elif choice == '8':
            show_live_key_expiry()
            continue

        elif choice == '9':
            _exit_screen(data_path)
            break

        else:
            console.print('[bold bright_red]❌ Invalid choice![/]')
            time.sleep(2)


if __name__ == '__main__':
    try:
        main_menu()
    except KeyboardInterrupt:
        console.print('\n[bold bright_yellow]⚠️  Interrupted. Exiting...[/]')
        sys.exit(0)
    except Exception as e:
        console.print(f'[bold bright_red]💥 ERROR:[/] {escape(str(e))}')
        import traceback
        traceback.print_exc()
        safe_input('\nPress Enter to exit...')
        sys.exit(1)