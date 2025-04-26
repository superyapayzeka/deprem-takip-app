# -*- coding: utf-8 -*-
import sys
import os # resource_path için gerekli
import requests
import json
import folium
import geopy.distance
import tempfile
# import os # Zaten yukarıda import edildi
import datetime
import logging
import configparser
import traceback
import threading
import platform

# Gerekli PySide6 modülleri
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout, QFormLayout,
    QListWidget, QListWidgetItem, QLabel, QPushButton, QStatusBar, QSplitter, QTabWidget,
    QDoubleSpinBox, QSpinBox, QLineEdit, QCheckBox, QComboBox, QSlider, QTextEdit,
    QMessageBox, QFileDialog,
    QSystemTrayIcon, QMenu
)
from PySide6.QtWebEngineWidgets import QWebEngineView
from PySide6.QtWebEngineCore import QWebEnginePage, QWebEngineSettings
from PySide6.QtCore import QUrl, QFileInfo, Qt, Slot, QTimer, QSettings, QStandardPaths, QCoreApplication
from PySide6.QtGui import QIcon, QPalette, QColor, QFont, QAction

# Ses ve Bildirim için
from plyer import notification
try:
    from playsound import playsound
    PLAYSOUND_AVAILABLE = True
except ImportError:
    PLAYSOUND_AVAILABLE = False
    print("Uyarı: 'playsound' kütüphanesi bulunamadı. Bildirim sesleri çalınamayacak. Yüklemek için: pip install playsound==1.2.2")

# --- Yardımcı Fonksiyon: Paketlendiğinde dosya yolunu bulmak için ---
def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    try:
        # PyInstaller creates a temp folder and stores path in _MEIPASS
        base_path = sys._MEIPASS
        # logging.info(f"Kaynak yolu _MEIPASS kullanılarak çözümleniyor: {base_path}") # Çok fazla log üretebilir
    except Exception:
        # _MEIPASS ayarlı değilse, normal geliştirme modundayız demektir
        base_path = os.path.dirname(os.path.abspath(__file__))
        # logging.info(f"Kaynak yolu geliştirme modu kullanılarak çözümleniyor: {base_path}")

    joined_path = os.path.join(base_path, relative_path)
    # logging.info(f"Kaynak için tam yol '{relative_path}': {joined_path}") # Çok fazla log üretebilir
    return joined_path
# -------------------------------------------------------------------

# --- Logging Setup ---
log_format = '%(asctime)s - %(levelname)s - %(message)s'
logging.basicConfig(level=logging.INFO, format=log_format)
log_stream = ""

class QtLogHandler(logging.Handler):
    def __init__(self, slot_func): super().__init__(); self.slot_func = slot_func
    def emit(self, record):
        try:
            msg = self.format(record); global log_stream; log_stream += msg + "\n"
            if self.slot_func: QTimer.singleShot(0, lambda m=msg: self.slot_func(m))
        except Exception as e: print(f"Loglama hatası: {e}")

# --- Constants & Defaults ---
APP_NAME = "Deprem Takip Uygulaması"; SETTINGS_FILE = "deprem_takip_ayarlar.ini"
USGS_API_URL = "https://earthquake.usgs.gov/earthquakes/feed/v1.0/summary/all_day.geojson"
DEFAULT_MIN_MAGNITUDE = 3.0; DEFAULT_CHECK_INTERVAL_MIN = 5
DEFAULT_TARGET_LAT = 41.0082; DEFAULT_TARGET_LON = 28.9784
DEFAULT_RADIUS_KM = 150; DEFAULT_NOTIFICATIONS_ENABLED = True
DEFAULT_NOTIFICATION_SOUND = "default_notification.wav"; DEFAULT_THEME = "dark-blue"
MAX_RADIUS_KM = 20001
APP_ICON_FILE = 'notification_icon.ico'

# --- Helper Functions ---
def get_earthquake_data(url=USGS_API_URL):
    logging.info(f"Deprem verisi çekiliyor: {url}")
    try:
        response = requests.get(url, timeout=25); response.raise_for_status()
        data = response.json(); features = data.get('features', [])
        logging.info(f"{len(features)} adet ham deprem verisi alındı."); valid_feature_count = 0
        for feature in features:
            props = feature.get('properties', {});
            if props.get('mag') is None: props['mag'] = 0.0
            time_ms = props.get('time')
            if time_ms:
                try: props['time_dt'] = datetime.datetime.fromtimestamp(time_ms / 1000, tz=datetime.timezone.utc); valid_feature_count += 1
                except (OSError, ValueError): props['time_dt'] = None
            else: props['time_dt'] = None
        if len(features) != valid_feature_count: logging.warning(f"{len(features)-valid_feature_count} deprem verisi eksik işlendi.")
        return features
    except requests.exceptions.Timeout: logging.error("Hata: API zaman aşımı.", exc_info=False); return None
    except requests.exceptions.RequestException as e: logging.error(f"Hata: API bağlantı: {e}", exc_info=False); return None
    except json.JSONDecodeError: logging.error("Hata: JSON formatı.", exc_info=False); return None
    except Exception as e: logging.error(f"Hata (veri çekme): {e}", exc_info=True); return None

def calculate_distance(coord1, coord2):
    if not coord1 or not coord2: return float('inf')
    try: return geopy.distance.geodesic(coord1, coord2).km
    except Exception as e: logging.error(f"Mesafe hatası: {e}"); return float('inf')

def format_datetime(dt):
    if dt: return dt.strftime('%Y-%m-%d %H:%M:%S')
    return "N/A"

# --- Ana Uygulama Penceresi ---
class EarthquakeMainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.earthquake_data = []; self.last_checked_ids = set(); self.current_map_file = None
        self.settings = {}; self.map_view = None; self.log_text_edit = None
        self._log_handler = None; self.nearby_list_widget = None
        self.tray_icon = None

        self.setWindowTitle(APP_NAME); self.setGeometry(50, 50, 1300, 850)

        # *** DEĞİŞİKLİK: İkon yolunu resource_path ile al ***
        try:
            self.icon_path = resource_path(APP_ICON_FILE)
            if os.path.exists(self.icon_path):
                 self.setWindowIcon(QIcon(self.icon_path))
                 logging.info(f"Uygulama ikonu yüklendi: {self.icon_path}")
            else:
                 logging.warning(f"Uygulama ikonu bulunamadı: {self.icon_path}")
                 self.icon_path = None
        except Exception as icon_err:
            logging.error(f"İkon yolu alınırken hata: {icon_err}")
            self.icon_path = None
        # ***************************************************

        self.load_settings(); self.init_ui(); self.apply_theme(self.settings.get('theme', DEFAULT_THEME))
        self.setup_tray_icon()

        self.check_timer = QTimer(self); self.check_timer.timeout.connect(self.check_for_earthquakes_slot)
        self.start_timer(); QTimer.singleShot(500, self.perform_initial_load)
        logging.info("Ana Pencere başlatıldı.")

    def init_ui(self):
        logging.info("Arayüz oluşturuluyor..."); self.tab_widget = QTabWidget(); self.setCentralWidget(self.tab_widget)
        self.log_tab = self.create_log_tab(); self.settings_tab = self.create_settings_tab()
        self.nearby_tab = self.create_nearby_tab(); self.map_tab = self.create_map_tab()
        self._log_handler = QtLogHandler(self.update_log_display); self._log_handler.setFormatter(logging.Formatter(log_format))
        logging.getLogger().addHandler(self._log_handler); logging.getLogger().setLevel(logging.INFO)
        self.tab_widget.addTab(self.settings_tab, "Ayarlar"); self.tab_widget.addTab(self.nearby_tab, "Yakındaki Depremler")
        self.tab_widget.addTab(self.map_tab, "Harita"); self.tab_widget.addTab(self.log_tab, "Log")
        self.status_bar = QStatusBar(); self.setStatusBar(self.status_bar); self.status_bar.showMessage("Arayüz başlatılıyor...")
        logging.info("Arayüz başarıyla oluşturuldu.")

    def setup_tray_icon(self):
        if not QSystemTrayIcon.isSystemTrayAvailable(): logging.warning("Sistem tepsisi desteklenmiyor."); return
        if self.icon_path:
            self.tray_icon = QSystemTrayIcon(QIcon(self.icon_path), self)
            self.tray_icon.setToolTip(f"{APP_NAME}\nÇift tıkla: Göster/Gizle")
            tray_menu = QMenu(self); show_hide_action = QAction("Göster/Gizle", self)
            show_hide_action.triggered.connect(self.toggle_window_visibility); tray_menu.addAction(show_hide_action)
            tray_menu.addSeparator(); quit_action = QAction("Çıkış", self)
            quit_action.triggered.connect(self.quit_application); tray_menu.addAction(quit_action)
            self.tray_icon.setContextMenu(tray_menu); self.tray_icon.activated.connect(self.tray_icon_activated)
            self.tray_icon.show(); logging.info("Sistem tepsisi ikonu oluşturuldu.")
        else: logging.error("Sistem tepsisi ikonu için ikon dosyası bulunamadı."); self.tray_icon = None

    @Slot(QSystemTrayIcon.ActivationReason)
    def tray_icon_activated(self, reason):
        if reason == QSystemTrayIcon.Trigger or reason == QSystemTrayIcon.DoubleClick: self.toggle_window_visibility()

    @Slot()
    def toggle_window_visibility(self):
        if self.isVisible(): self.hide(); logging.info("Pencere gizlendi.")
        else: self.show(); self.activateWindow(); self.raise_(); logging.info("Pencere gösterildi.")

    @Slot()
    def quit_application(self):
        logging.info("Çıkış menüsünden uygulama kapatılıyor..."); self.check_timer.stop()
        if self.tray_icon: self.tray_icon.hide()
        QApplication.quit()

    def create_settings_tab(self):
        widget = QWidget(); layout = QVBoxLayout(widget); form_layout = QFormLayout()
        magnitude_layout = QHBoxLayout(); self.magnitude_slider = QSlider(Qt.Horizontal); self.magnitude_slider.setRange(10, 90); self.magnitude_slider.setSingleStep(1)
        initial_mag = self.settings.get('min_magnitude', DEFAULT_MIN_MAGNITUDE); self.magnitude_slider.setValue(int(initial_mag * 10))
        self.magnitude_label = QLabel(f"{initial_mag:.1f}"); self.magnitude_slider.valueChanged.connect(lambda val: self.magnitude_label.setText(f"{val / 10.0:.1f}"))
        magnitude_layout.addWidget(self.magnitude_slider); magnitude_layout.addWidget(self.magnitude_label); form_layout.addRow("Min. Büyüklük:", magnitude_layout)
        self.interval_spinbox = QSpinBox(); self.interval_spinbox.setRange(1, 120); self.interval_spinbox.setValue(self.settings.get('check_interval_min', DEFAULT_CHECK_INTERVAL_MIN))
        form_layout.addRow("Kontrol Aralığı (dk):", self.interval_spinbox)
        location_layout = QHBoxLayout(); self.lat_input = QLineEdit(str(self.settings.get('target_lat', DEFAULT_TARGET_LAT)))
        self.lon_input = QLineEdit(str(self.settings.get('target_lon', DEFAULT_TARGET_LON)))
        location_layout.addWidget(self.lat_input); location_layout.addWidget(self.lon_input); form_layout.addRow("Hedef Konum (Enlem, Boylam):", location_layout)
        self.radius_input = QSpinBox(); self.radius_input.setRange(10, MAX_RADIUS_KM); self.radius_input.setSingleStep(10)
        self.radius_input.setValue(self.settings.get('radius_km', DEFAULT_RADIUS_KM)); form_layout.addRow("Yarıçap (km):", self.radius_input)
        self.notifications_checkbox = QCheckBox("Bildirimleri Etkinleştir (Dünya Geneli)"); self.notifications_checkbox.setChecked(self.settings.get('notifications_enabled', DEFAULT_NOTIFICATIONS_ENABLED))
        form_layout.addRow(self.notifications_checkbox)
        sound_layout = QHBoxLayout(); sound_file_path = self.settings.get('notification_sound', "")
        # *** DEĞİŞİKLİK: Varsayılan ses yolu kontrolü resource_path ile ***
        is_default_sound = os.path.basename(sound_file_path) == DEFAULT_NOTIFICATION_SOUND
        try: default_sound_full_path = resource_path(DEFAULT_NOTIFICATION_SOUND)
        except Exception: default_sound_full_path = "" # Hata olursa boş kalsın
        # **************************************************************
        if sound_file_path and os.path.exists(sound_file_path): sound_display_name = os.path.basename(sound_file_path); tooltip_path = sound_file_path
        elif is_default_sound and os.path.exists(default_sound_full_path): sound_display_name = DEFAULT_NOTIFICATION_SOUND; tooltip_path = default_sound_full_path; self.settings['notification_sound'] = tooltip_path
        else: sound_display_name = "Seçilmedi"; tooltip_path = ""
        self.sound_label = QLabel(sound_display_name); self.sound_label.setToolTip(tooltip_path)
        self.sound_button = QPushButton("Ses Seç..."); self.sound_button.clicked.connect(self.select_sound_file)
        self.clear_sound_button = QPushButton("Temizle"); self.clear_sound_button.clicked.connect(self.clear_sound_file)
        sound_layout.addWidget(self.sound_label, stretch=1); sound_layout.addWidget(self.sound_button); sound_layout.addWidget(self.clear_sound_button); form_layout.addRow("Bildirim Sesi:", sound_layout)
        theme_layout = QHBoxLayout(); self.theme_combobox = QComboBox(); self.theme_combobox.addItems(["dark-blue", "dark-orange", "light-blue", "light-gray"])
        self.theme_combobox.setCurrentText(self.settings.get('theme', DEFAULT_THEME)); theme_layout.addWidget(QLabel("Tema:")); theme_layout.addWidget(self.theme_combobox)
        form_layout.addRow("Görünüm:", theme_layout)
        self.save_settings_button = QPushButton("Ayarları Kaydet ve Uygula"); self.save_settings_button.clicked.connect(self.save_and_apply_settings)
        layout.addLayout(form_layout); layout.addStretch(); layout.addWidget(self.save_settings_button, alignment=Qt.AlignCenter)
        return widget

    def create_nearby_tab(self):
        widget = QWidget(); layout = QVBoxLayout(widget)
        label = QLabel("Hedef konuma yakın (ayarlanan yarıçap içinde) ve minimum büyüklükteki depremler:")
        self.nearby_list_widget = QListWidget()
        self.nearby_list_widget.currentItemChanged.connect(self.focus_map_on_list_item)
        layout.addWidget(label); layout.addWidget(self.nearby_list_widget)
        return widget

    def create_map_tab(self):
        widget = QWidget(); self.map_layout = QVBoxLayout(widget); self.map_layout.setContentsMargins(0, 0, 0, 0)
        loading_label = QLabel("Harita başlatılıyor..."); loading_label.setAlignment(Qt.AlignCenter)
        self.map_layout.addWidget(loading_label); logging.info("Harita sekmesi oluşturuldu (WebEngineView henüz eklenmedi).")
        return widget

    def initialize_map_view(self):
        if self.map_view is None:
            try:
                logging.info("QWebEngineView başlatılıyor...")
                self.map_view = QWebEngineView()
                logging.info("QWebEngineView başarıyla oluşturuldu.")
                settings = self.map_view.settings()
                if settings:
                    try: settings.setAttribute(QWebEngineSettings.WebAttribute.JavascriptEnabled, True); logging.info("WebEngine Ayarları: Javascript=True")
                    except AttributeError:
                        try: settings.setAttribute(QWebEngineSettings.JavascriptEnabled, True); logging.info("WebEngine Ayarları: Javascript=True (doğrudan denendi)")
                        except AttributeError: logging.warning("JavascriptEnabled attribute'u ayarlanamadı.")
                else: logging.warning("WebEngine ayarları alınamadı!")
                if self.map_view.page(): self.map_view.page().loadFinished.connect(self.map_load_finished); logging.info("QWebEnginePage.loadFinished sinyali bağlandı.")
                else: logging.warning("QWebEngineView sayfası alınamadı, loadFinished sinyali bağlanamadı.")
                item = self.map_layout.takeAt(0)
                if item and item.widget(): item.widget().deleteLater()
                self.map_layout.addWidget(self.map_view)
                self.map_view.setHtml("<html><body style='background-color:#333; color:white; text-align:center; padding-top: 50px;'>Harita verisi bekleniyor...</body></html>")
            except Exception as e:
                logging.critical("QWebEngineView OLUŞTURULURKEN KRİTİK HATA!", exc_info=True)
                QMessageBox.critical(self, "Harita Hatası", f"Harita bileşeni başlatılamadı:\n{e}\n\nHarita sekmesi kullanılamayabilir.")
                item = self.map_layout.itemAt(0)
                if item and item.widget(): item.widget().setText("Harita yüklenemedi.")

    @Slot(bool)
    def map_load_finished(self, success):
        if success:
            logging.info("Harita sayfası başarıyla yüklendi (loadFinished=True).")
            if self.map_view and self.map_view.page():
                self.map_view.page().runJavaScript("document.body.style.border='5px solid lime'; console.log('JavaScript test executed!');", self.javascript_callback)
        else: logging.error("Harita sayfası yüklenirken HATA oluştu (loadFinished=False).")

    def javascript_callback(self, result): logging.info(f"JavaScript test sonucu: {result}")

    def create_log_tab(self):
        widget = QWidget(); layout = QVBoxLayout(widget); self.log_text_edit = QTextEdit(); self.log_text_edit.setReadOnly(True)
        self.log_text_edit.setFont(QFont("Courier New", 9)); self.log_text_edit.setText(log_stream); layout.addWidget(self.log_text_edit)
        return widget

    def load_settings(self):
        config = configparser.ConfigParser(interpolation=None)
        default_settings = {'min_magnitude': DEFAULT_MIN_MAGNITUDE, 'check_interval_min': DEFAULT_CHECK_INTERVAL_MIN,'target_lat': DEFAULT_TARGET_LAT, 'target_lon': DEFAULT_TARGET_LON,'radius_km': DEFAULT_RADIUS_KM, 'notifications_enabled': DEFAULT_NOTIFICATIONS_ENABLED,'notification_sound': DEFAULT_NOTIFICATION_SOUND, 'theme': DEFAULT_THEME,}
        if not config.read(SETTINGS_FILE, encoding='utf-8'):
            logging.warning(f"{SETTINGS_FILE} bulunamadı. Varsayılan ayarlar kullanılacak."); self.settings = default_settings.copy()
            # *** DEĞİŞİKLİK: resource_path kullanımı ***
            try:
                default_sound_full_path = resource_path(DEFAULT_NOTIFICATION_SOUND)
                if os.path.exists(default_sound_full_path): self.settings['notification_sound'] = default_sound_full_path
                else: self.settings['notification_sound'] = ""
            except Exception as res_err:
                 logging.error(f"Varsayılan ses yolu alınamadı: {res_err}")
                 self.settings['notification_sound'] = ""
            # ******************************************
        else:
            logging.info(f"Ayarlar {SETTINGS_FILE} dosyasından yüklendi."); self.settings = default_settings.copy()
            if 'Settings' in config:
                cfg_sec = config['Settings']
                try:
                    self.settings.update({'min_magnitude': cfg_sec.getfloat('MinMagnitude', DEFAULT_MIN_MAGNITUDE),'check_interval_min': cfg_sec.getint('CheckIntervalMin', DEFAULT_CHECK_INTERVAL_MIN),'target_lat': cfg_sec.getfloat('TargetLat', DEFAULT_TARGET_LAT),'target_lon': cfg_sec.getfloat('TargetLon', DEFAULT_TARGET_LON),'radius_km': cfg_sec.getint('RadiusKm', DEFAULT_RADIUS_KM),'notifications_enabled': cfg_sec.getboolean('NotificationsEnabled', DEFAULT_NOTIFICATIONS_ENABLED),'notification_sound': cfg_sec.get('NotificationSound', ""),'theme': cfg_sec.get('Theme', DEFAULT_THEME),})
                    sound_path = self.settings['notification_sound']
                    # *** DEĞİŞİKLİK: resource_path kullanımı ***
                    if sound_path and not os.path.dirname(sound_path) and os.path.basename(sound_path) == DEFAULT_NOTIFICATION_SOUND:
                        try:
                            potential_path = resource_path(sound_path)
                            if os.path.exists(potential_path): sound_path = potential_path
                            else: sound_path = ""; self.settings['notification_sound'] = sound_path
                        except Exception: sound_path = ""; self.settings['notification_sound'] = ""
                    elif sound_path and not os.path.exists(sound_path): logging.warning(f"Ayarlardan okunan ses dosyası bulunamadı: {sound_path}"); self.settings['notification_sound'] = ""
                    # ******************************************
                except (ValueError, configparser.Error) as e: logging.error(f"Ayarlar okunurken hata: {e}. Varsayılanlar kullanılacak.", exc_info=False); self.settings = default_settings
            else: logging.warning(f"{SETTINGS_FILE} dosyasında [Settings] bölümü bulunamadı.")

    def save_settings(self):
        config = configparser.ConfigParser(interpolation=None)
        config['Settings'] = {'MinMagnitude': str(self.settings['min_magnitude']),'CheckIntervalMin': str(self.settings['check_interval_min']),'TargetLat': str(self.settings['target_lat']),'TargetLon': str(self.settings['target_lon']),'RadiusKm': str(self.settings['radius_km']),'NotificationsEnabled': str(self.settings['notifications_enabled']),'NotificationSound': str(self.settings['notification_sound']),'Theme': str(self.settings['theme']),}
        try:
            with open(SETTINGS_FILE, 'w', encoding='utf-8') as configfile: config.write(configfile)
            logging.info(f"Ayarlar {SETTINGS_FILE} dosyasına kaydedildi."); self.status_bar.showMessage("Ayarlar kaydedildi.", 3000)
        except IOError as e: logging.error(f"Ayarlar kaydedilemedi: {e}"); QMessageBox.warning(self, "Hata", f"Ayarlar dosyaya yazılamadı:\n{e}")

    @Slot()
    def save_and_apply_settings(self):
        logging.info("Ayarlar kaydediliyor ve uygulanıyor...")
        try:
            self.settings['min_magnitude'] = self.magnitude_slider.value() / 10.0; self.settings['check_interval_min'] = self.interval_spinbox.value()
            self.settings['target_lat'] = float(self.lat_input.text().replace(',', '.')); self.settings['target_lon'] = float(self.lon_input.text().replace(',', '.'))
            self.settings['radius_km'] = self.radius_input.value(); self.settings['notifications_enabled'] = self.notifications_checkbox.isChecked()
            self.settings['notification_sound'] = self.sound_label.toolTip() if self.sound_label.toolTip() else ""; self.settings['theme'] = self.theme_combobox.currentText()
            self.apply_theme(self.settings['theme']); self.start_timer(); self.save_settings()
            self.check_for_earthquakes(is_initial_load=True, force_update=True)
            logging.info("Ayarlar başarıyla uygulandı ve kaydedildi.")
        except ValueError as e: logging.error(f"Ayarları okurken geçersiz değer: {e}"); QMessageBox.warning(self, "Geçersiz Değer", f"Lütfen sayısal alanlara geçerli değerler girin.\n{e}")
        except Exception as e: logging.error(f"Ayarlar kaydedilirken/uygulanırken hata: {e}", exc_info=True); QMessageBox.critical(self, "Hata", f"Ayarlar uygulanırken bir sorun oluştu:\n{e}")

    @Slot()
    def select_sound_file(self):
        current_path = self.sound_label.toolTip(); start_dir = os.path.dirname(current_path) if current_path and os.path.exists(os.path.dirname(current_path)) else QStandardPaths.writableLocation(QStandardPaths.MusicLocation)
        file_path, _ = QFileDialog.getOpenFileName(self, "Bildirim Ses Dosyası Seç", start_dir, "Ses Dosyaları (*.wav *.mp3)")
        if file_path: self.sound_label.setText(os.path.basename(file_path)); self.sound_label.setToolTip(file_path); logging.info(f"Bildirim sesi seçildi: {file_path}")

    @Slot()
    def clear_sound_file(self):
        self.sound_label.setText("Seçilmedi"); self.sound_label.setToolTip(""); logging.info("Bildirim sesi temizlendi.")

    def get_stylesheet(self, theme_name):
        base_style = """ QWidget { font-size: 10pt; } QPushButton { padding: 6px 12px; } QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QTextEdit, QListWidget { padding: 4px; border: 1px solid #555; } QStatusBar { font-size: 9pt; } QTabWidget::pane { border: 1px solid #444; } QTabBar::tab { padding: 8px 15px; } """
        dark_colors = { "bg": "#2E2E2E", "bg_alt": "#3C3C3C", "text": "#E0E0E0", "border": "#555", "highlight": "#5A9BFF", "button": "#4A4A4A", "button_hover": "#5A5A5A", "button_text": "#E0E0E0" }
        light_colors = { "bg": "#F0F0F0", "bg_alt": "#E0E0E0", "text": "#1E1E1E", "border": "#B0B0B0", "highlight": "#0078D7", "button": "#D0D0D0", "button_hover": "#C0C0C0", "button_text": "#1E1E1E" }
        colors = dark_colors if "dark" in theme_name else light_colors
        if "blue" in theme_name: colors["highlight"] = dark_colors["highlight"] if "dark" in theme_name else light_colors["highlight"]
        elif "orange" in theme_name: colors["highlight"] = "#FFA500"
        elif "green" in theme_name: colors["highlight"] = "#4CAF50"
        qss = base_style + f""" QMainWindow, QWidget {{ background-color: {colors['bg']}; color: {colors['text']}; }} QTabWidget::pane {{ background-color: {colors['bg_alt']}; border-color: {colors['border']}; }} QTabBar::tab {{ background-color: {colors['button']}; color: {colors['button_text']}; border: 1px solid {colors['border']}; margin-right: 2px; border-bottom: none; }} QTabBar::tab:selected {{ background-color: {colors['bg_alt']}; border-bottom: 2px solid {colors['highlight']}; }} QTabBar::tab:hover {{ background-color: {colors['button_hover']}; }} QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QTextEdit, QListWidget {{ background-color: {colors['bg_alt']}; color: {colors['text']}; border-color: {colors['border']}; }} QTextEdit, QListWidget {{ border-radius: 3px; }} QPushButton {{ background-color: {colors['button']}; color: {colors['button_text']}; border: 1px solid {colors['border']}; border-radius: 3px; }} QPushButton:hover {{ background-color: {colors['button_hover']}; }} QPushButton:pressed {{ background-color: {colors['highlight']}; color: {colors['bg']}; }} QSlider::groove:horizontal {{ height: 5px; background: {colors['bg_alt']}; border-radius: 2px; border: 1px solid {colors['border']}; }} QSlider::handle:horizontal {{ background: {colors['highlight']}; border: 1px solid {colors['highlight']}; width: 14px; height: 14px; margin: -5px 0; border-radius: 7px; }} QSlider::sub-page:horizontal {{ background: {colors['highlight']}; border-radius: 2px; }} QCheckBox::indicator {{ width: 16px; height: 16px; }} QCheckBox::indicator:unchecked {{ border: 1px solid {colors['border']}; background-color: {colors['bg_alt']}; }} QCheckBox::indicator:checked {{ background-color: {colors['highlight']}; border: 1px solid {colors['highlight']}; }} QStatusBar {{ background-color: {colors['bg_alt']}; border-top: 1px solid {colors['border']}; }} QListWidget::item:selected {{ background-color: {colors['highlight']}; color: {colors['bg']}; }} QMessageBox {{ background-color: {colors['bg_alt']}; }} """
        return qss

    def apply_theme(self, theme_name): stylesheet = self.get_stylesheet(theme_name); self.setStyleSheet(stylesheet); logging.info(f"Tema uygulandı: {theme_name}")

    @Slot()
    def check_for_earthquakes_slot(self): logging.info("Periyodik kontrol tetiklendi."); self.check_for_earthquakes()

    def start_timer(self):
        interval_ms = self.settings.get('check_interval_min', DEFAULT_CHECK_INTERVAL_MIN) * 60 * 1000
        if self.check_timer.isActive(): self.check_timer.stop()
        if interval_ms > 0: self.check_timer.start(interval_ms); logging.info(f"Zamanlayıcı {interval_ms / 60000:.1f} dakika aralıkla başlatıldı.")
        else: logging.warning("Geçersiz kontrol aralığı, zamanlayıcı başlatılmadı.")

    def perform_initial_load(self):
        logging.info("Başlangıç yüklemesi yapılıyor...")
        if self.map_view is None: self.initialize_map_view()
        self.check_for_earthquakes(is_initial_load=True, force_update=True)

    def check_for_earthquakes(self, is_initial_load=False, force_update=False):
        self.status_bar.showMessage("Deprem verileri güncelleniyor...", 3000); QApplication.processEvents()
        new_data = get_earthquake_data();
        if new_data is None: self.status_bar.showMessage("Deprem verileri alınamadı!", 5000); return
        if not force_update and new_data == self.earthquake_data: logging.info("Deprem verilerinde değişiklik yok."); self.status_bar.showMessage("Veriler güncel.", 3000); return
        self.earthquake_data = new_data; newly_found_significant = []; current_ids = set()
        target_location = (self.settings.get('target_lat'), self.settings.get('target_lon')); radius_km = self.settings.get('radius_km'); min_magnitude = self.settings.get('min_magnitude')
        for eq in self.earthquake_data:
            eq_id = eq.get('id');
            if eq_id: current_ids.add(eq_id)
            else: continue
            properties = eq.get('properties', {}); magnitude = properties.get('mag', 0.0)
            if magnitude >= min_magnitude and eq_id not in self.last_checked_ids: newly_found_significant.append(eq)
            geometry = eq.get('geometry', {}); coordinates = geometry.get('coordinates')
            if coordinates:
                eq_location = (coordinates[1], coordinates[0]); distance = calculate_distance(target_location, eq_location)
                if distance != float('inf'): eq['distance_from_target'] = distance
            elif 'distance_from_target' in eq: del eq['distance_from_target']
        newly_checked_ids = current_ids - self.last_checked_ids; self.last_checked_ids.update(current_ids)
        if not is_initial_load and self.settings.get('notifications_enabled'):
            for eq in newly_found_significant: self.send_notification(eq)
        self.update_ui_with_data(); total_count = len(self.earthquake_data)
        self.status_bar.showMessage(f"Veriler güncellendi. Toplam: {total_count}.", 5000)

    def update_ui_with_data(self):
        logging.info("Arayüz verilerle güncelleniyor...")
        self.update_nearby_list()
        if self.map_view: self.update_map()
        else: logging.warning("Harita görünümü henüz başlatılmadığı için harita güncellenemedi.")

    def update_nearby_list(self):
        if not self.nearby_list_widget: return
        logging.info("Yakındaki depremler listesi güncelleniyor..."); self.nearby_list_widget.clear(); nearby_count = 0
        target_location = (self.settings.get('target_lat'), self.settings.get('target_lon')); radius_km = self.settings.get('radius_km'); min_magnitude = self.settings.get('min_magnitude')
        filtered_for_list = []
        for eq in self.earthquake_data:
            properties = eq.get('properties', {}); magnitude = properties.get('mag', 0.0)
            if magnitude >= min_magnitude and 'distance_from_target' in eq and eq['distance_from_target'] <= radius_km: filtered_for_list.append(eq)
        sorted_list = sorted(filtered_for_list, key=lambda x: x.get('distance_from_target', float('inf')))
        for eq in sorted_list:
            properties = eq['properties']; mag = properties['mag']; place = properties['place']; time_str = format_datetime(properties.get('time_dt'))
            dist = eq['distance_from_target']; dist_str = f"~{dist:.0f} km"
            list_item_text = f"[{time_str[11:16]}] B:{mag:.1f} ({dist_str}) - {place}"; list_item = QListWidgetItem(list_item_text)
            list_item.setData(Qt.UserRole, eq); self.nearby_list_widget.addItem(list_item); nearby_count += 1
        logging.info(f"{nearby_count} deprem yakındaki listesine eklendi.")

    def update_map(self):
        if not self.map_view: logging.warning("Harita güncellenemiyor..."); return
        if not self.earthquake_data: logging.warning("Harita için veri yok."); self.map_view.setHtml("<html><body>Veri yok.</body></html>"); return
        self.status_bar.showMessage("Harita oluşturuluyor...", 2000); QApplication.processEvents()
        target_location = (self.settings.get('target_lat'), self.settings.get('target_lon')); radius_km = self.settings.get('radius_km'); min_magnitude = self.settings.get('min_magnitude')
        filtered_earthquakes = []
        logging.info(f"Harita için filtreleme: MinMag={min_magnitude}, Yarıçap={radius_km} km, Hedef={target_location}")
        for eq in self.earthquake_data:
             properties = eq.get('properties', {}); magnitude = properties.get('mag', 0.0)
             if magnitude >= min_magnitude:
                 if 'distance_from_target' in eq and eq['distance_from_target'] <= radius_km: filtered_earthquakes.append(eq)
                 elif 'distance_from_target' not in eq:
                      geometry = eq.get('geometry', {}); coordinates = geometry.get('coordinates')
                      if coordinates:
                           eq_location = (coordinates[1], coordinates[0]); distance = calculate_distance(target_location, eq_location)
                           if distance <= radius_km: eq['distance_from_target'] = distance; filtered_earthquakes.append(eq)
        logging.info(f"Harita için {len(filtered_earthquakes)} deprem filtrelendi.")
        map_center = target_location
        if radius_km < 100: zoom = 9
        elif radius_km < 300: zoom = 8
        elif radius_km < 700: zoom = 7
        elif radius_km < 1500: zoom = 6
        else: zoom = 5
        if not filtered_earthquakes: logging.info("Filtrelenen deprem yok, harita sadece hedef konumu gösterecek.")
        m = folium.Map(location=map_center, zoom_start=zoom, tiles="OpenStreetMap")
        logging.info("Folium haritası 'OpenStreetMap' tiles ile oluşturuluyor.")
        folium.Marker(location=target_location, popup="Hedef Konum", icon=folium.Icon(color='red', icon='screenshot')).add_to(m)
        folium.Circle(location=target_location, radius=radius_km * 1000, color='red', fill=False, weight=2, dash_array='5, 5', tooltip=f"{radius_km} km Yarıçap").add_to(m)
        for eq in filtered_earthquakes:
            props = eq['properties']; coords = eq['geometry']['coordinates']; mag = props['mag']; place = props['place']
            time_str = format_datetime(props.get('time_dt')); depth = coords[2]; dist = eq.get('distance_from_target', -1)
            dist_str = f"{dist:.1f} km" if dist >= 0 else "N/A"
            popup_html = f"<b>Yer:</b> {place}<br><b>Büyüklük:</b> {mag:.1f}<br><b>Derinlik:</b> {depth:.1f} km<br><b>Zaman:</b> {time_str}<br><b>Hedefe Uzaklık:</b> {dist_str}"
            color = 'red' if mag >= 4.0 else 'orange'; radius_size = 3 + mag
            folium.CircleMarker(location=[coords[1], coords[0]], radius=radius_size, popup=folium.Popup(popup_html, max_width=300), tooltip=f"{mag:.1f} - {place[:40]}...", color=color, fill=True, fill_color=color, fill_opacity=0.6).add_to(m)
        try:
            html_content = m.get_root().render()
            logging.info(f"Harita HTML içeriği oluşturuldu (uzunluk: {len(html_content)}).")
            self.map_view.setHtml(html_content, QUrl("qrc:/"))
            logging.info("Harita içeriği setHtml ile yüklendi.")
            self.current_map_file = None
        except Exception as e:
            logging.error(f"Harita oluşturulurken/setHtml ile yüklenirken hata: {e}", exc_info=True)
            self.map_view.setHtml("<html><body style='color:red;'>Harita oluşturulurken hata oluştu.</body></html>")

    def send_notification(self, earthquake_data):
        props = earthquake_data['properties']; mag = props.get('mag', 0.0); place = props.get('place', 'Bilinmeyen yer'); time_str = format_datetime(props.get('time_dt')); dist_str = ""
        if 'distance_from_target' in earthquake_data: dist = earthquake_data['distance_from_target']; dist_str = f" (Hedefe ~{dist:.0f} km)" if dist >= 0 else ""
        title = f"Deprem Bildirimi: {mag:.1f}"; message = f"{place}{dist_str}\n{time_str}"
        logging.info(f"Bildirim gönderiliyor: {title} - {message}")
        # *** DEĞİŞİKLİK: İkon yolunu resource_path ile al ***
        icon_to_use = None
        try:
             potential_icon_path = resource_path(APP_ICON_FILE)
             if os.path.exists(potential_icon_path):
                  icon_to_use = potential_icon_path
                  logging.info(f"Bildirim ikonu kullanılacak: {icon_to_use}")
             else:
                  logging.warning(f"Bildirim ikonu bulunamadı: {potential_icon_path}")
        except Exception as icon_err:
             logging.error(f"Bildirim ikonu yolu alınırken hata: {icon_err}")
        # *******************************************************
        try:
            try:
                notification.notify(
                    title=title, message=message, app_name=APP_NAME,
                    app_icon=icon_to_use, # İkon yolunu kullan
                    timeout=15)
            except Exception as notify_err: logging.error(f"Plyer bildirimi gönderilemedi: {notify_err}")
            sound_file = self.settings.get('notification_sound')
            # *** DEĞİŞİKLİK: Ses yolu kontrolü ***
            # Ayarlardaki yol tam yol olmalı (load_settings ve select/clear ile sağlanıyor)
            if sound_file and PLAYSOUND_AVAILABLE and os.path.exists(sound_file):
            # ************************************
                try: sound_thread = threading.Thread(target=playsound, args=(sound_file,), daemon=True); sound_thread.start(); logging.info(f"Bildirim sesi çalınıyor (thread): {sound_file}")
                except Exception as e: logging.error(f"Bildirim sesi çalınamadı ({sound_file}): {e}", exc_info=False)
            elif sound_file: logging.warning(f"Ses dosyası '{sound_file}' bulunamadı veya playsound yok.")
        except Exception as e: logging.error(f"Bildirim işlemi sırasında hata: {e}", exc_info=False)

    @Slot(QListWidgetItem, QListWidgetItem)
    def focus_map_on_list_item(self, current_item, previous_item):
        if current_item and self.map_view and self.map_view.page():
            eq_data = current_item.data(Qt.UserRole)
            if eq_data:
                geometry = eq_data.get('geometry', {}); coordinates = geometry.get('coordinates')
                if coordinates:
                    lat, lon = coordinates[1], coordinates[0]
                    js_code = f"if (typeof map !== 'undefined') {{ map.setView([{lat}, {lon}], 10); }} else {{ console.warn('Leaflet map object (map) not found for focusing.'); }}"
                    self.map_view.page().runJavaScript(js_code)
                    logging.info(f"Harita listesinden odaklanıyor: {lat:.4f}, {lon:.4f}")
                    map_tab_index = -1
                    for i in range(self.tab_widget.count()):
                        if self.tab_widget.widget(i) == self.map_tab: map_tab_index = i; break
                    if map_tab_index != -1: self.tab_widget.setCurrentIndex(map_tab_index)

    @Slot(str)
    def update_log_display(self, message):
        if self.log_text_edit: self.log_text_edit.append(message)

    # closeEvent (Tepsiye gönderme eklendi)
    def closeEvent(self, event):
        if self.tray_icon and self.tray_icon.isVisible():
            event.ignore(); self.hide()
            self.tray_icon.showMessage(APP_NAME,"Uygulama arka planda çalışıyor.", QSystemTrayIcon.Information, 2000)
            logging.info("Pencere kapatıldı (arka plana alındı).")
        else:
            logging.info("Uygulama kapatılıyor (tepsi ikonu yok/gizli)...")
            self.quit_application(); event.accept()

# --- Uygulama Başlangıcı ---
if __name__ == "__main__":
    try:
        os.environ["QTWEBENGINE_CHROMIUM_FLAGS"] = "--disable-gpu"; logging.info("Ortam değişkeni ayarlandı: QTWEBENGINE_CHROMIUM_FLAGS=--disable-gpu")
        if platform.system() == "Windows":
             QCoreApplication.setAttribute(Qt.AA_UseSoftwareOpenGL)
             logging.info("Windows algılandı, yazılım tabanlı rendering (AA_UseSoftwareOpenGL) deneniyor.")
    except Exception as e: logging.error(f"Başlangıç ayarları yapılırken hata: {e}")
    logging.info(f"{APP_NAME} başlatılıyor...")
    try: QApplication.setAttribute(Qt.AA_EnableHighDpiScaling); QApplication.setAttribute(Qt.AA_UseHighDpiPixmaps)
    except AttributeError: logging.warning("Bu Qt sürümünde DPI öznitelikleri desteklenmiyor olabilir.")

    QApplication.setQuitOnLastWindowClosed(False) # Pencere kapansa da çıkma

    app = QApplication(sys.argv); app.setOrganizationName("MyCompanyOrName"); app.setApplicationName(APP_NAME)
    try:
        window = EarthquakeMainWindow(); window.show(); logging.info("Olay döngüsü başlatılıyor...")
        sys.exit(app.exec())
    except Exception as e:
        logging.critical("Uygulama başlatılırken kritik hata!", exc_info=True)
        error_msg = f"Uygulamada kritik bir hata oluştu:\n\n{traceback.format_exc()}"
        try: QMessageBox.critical(None, "Kritik Hata", error_msg)
        except: print("\n\n" + error_msg + "\n")
        sys.exit(1)