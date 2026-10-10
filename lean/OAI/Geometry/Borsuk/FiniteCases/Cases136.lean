import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases135

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32741 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a47 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u2_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c32642 h h0 hv
  have u3_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32740 h h0 hv n105
  have u4_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32737 h h0 hv n105
  have u5_59 : T {1, 6, 7} := by
    by_contra hv
    exact c12998 h u4_200 hv u3_95 n105
  have u6_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32739 h h0 u3_95 hv n105
  have u7_80 : T {2, 6, 7} := by
    by_contra hv
    exact c13000 h u4_200 hv u3_95 n105
  have u8_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c28535 h u6_311 hv u5_59 u7_80
  have u9_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15638 h hv u8_31 u3_95 n105
  have u10_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16494 h hv u8_31 u3_95 n105
  have u11_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c12871 h u4_200 hv u7_80
  have u12_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c654 h hv u11_44
  have u13_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c28405 h u6_311 hv u7_80
  have u14_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c39 h hv u13_3
  have u15_38 : T {1, 2, 4} := by
    by_contra hv
    exact c12864 h u4_200 hv u3_95
  have u16_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31918 h h0 u4_200 hv u15_38
  have u17_88 : T {3, 4, 7} := by
    by_contra hv
    exact c12866 h u4_200 u16_40 hv
  have u18_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c592 h hv u16_40
  have u19_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c12881 h u4_200 u5_59 hv
  have u20_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28411 h u6_311 hv u5_59
  have u21_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32738 h h0 hv u3_95 n105
  have u22_36 : T {0, 8, 9} := by
    by_contra hv
    exact c536 h u4_200 hv
  have u23_30 : T {0, 5, 9} := by
    by_contra hv
    exact c450 h u4_200 hv
  have u24_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c1565 h hv n105
  have u25_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c31923 h h0 u4_200 hv a47
  have u26_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c12921 h u4_200 a47 hv u5_59
  have u27_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c12971 h u4_200 a47 hv u17_88
  have u28_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c12875 h u4_200 a47 hv
  have u29_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24219 h hv u23_30 a47
  have u30_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23521 h hv u22_36 a47
  have u31_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12906 h u4_200 u16_40 u25_46 hv
  have u32_73 : T {2, 4, 7} := by
    by_contra hv
    exact c12872 h u4_200 u25_46 hv
  have u33_67 : T {2, 3, 6} := by
    by_contra hv
    exact c12964 h u4_200 u25_46 hv u3_95
  have u34_12 : T {0, 2, 6} := by
    by_contra hv
    exact c28412 h u6_311 hv u26_52
  have u35_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20630 h hv u20_10 u19_65 u28_72
  have u36_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21332 h hv u20_10 u19_65 u28_72
  have u37_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c28415 h u6_311 hv u31_51
  have u38_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20399 h hv u0_24 u32_73 u17_88
  have u39_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21247 h hv u0_24 u32_73 u17_88
  have u40_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19091 h hv u34_12 u33_67 u7_80
  have u41_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19941 h hv u34_12 u33_67 u7_80
  have u42_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c859 h hv u9_219 u2_234 u40_244 u38_253 u35_255 u21_256
  have u43_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c949 h hv u10_225 u1_240 u41_250 u21_256 u39_259 u36_260
  have u44_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c947 h hv u43_148 u10_225 u1_240 u41_250 u21_256 u39_259 u36_260
  have u45_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c857 h hv u42_142 u9_219 u2_234 u40_244 u38_253 u35_255 u21_256
  have u46_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26310 h hv u37_13 u44_64
  have u47_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c10780 h hv u44_64 u27_68
  have u48_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27012 h hv u37_13 u45_58
  have u49_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11478 h hv u45_58 u27_68
  have u50_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c31537 h h0 hv u30_276 u46_296 u47_185
  have u51_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c31560 h h0 hv u49_190 u29_281 u48_301
  have u52_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c766 h hv u14_135 u18_212 u12_227 u50_241 u24_245 u51_246
  exact c752 h u31_51 u14_135 u18_212 u12_227 u50_241 u24_245 u51_246 u52_247

theorem c32742 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → False := by
  classical
  intro n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c32645 h h0 hv
  have u2_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c32642 h h0 hv
  have u3_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u4_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32737 h h0 hv n105
  have u6_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32740 h h0 hv n105
  have u7_38 : T {1, 2, 4} := by
    by_contra hv
    exact c12864 h u5_200 hv u6_95
  have u8_59 : T {1, 6, 7} := by
    by_contra hv
    exact c12998 h u5_200 hv u6_95 n105
  have u9_80 : T {2, 6, 7} := by
    by_contra hv
    exact c13000 h u5_200 hv u6_95 n105
  have u10_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32738 h h0 hv u6_95 n105
  have u11_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32739 h h0 u6_95 hv n105
  have u12_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31918 h h0 u5_200 hv u7_38
  have u13_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32525 h h0 hv u7_38 u11_311
  have u14_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28411 h u11_311 hv u8_59
  have u15_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c12881 h u5_200 u8_59 hv
  have u16_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c12871 h u5_200 hv u9_80
  have u17_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c28535 h u11_311 hv u8_59 u9_80
  have u18_88 : T {3, 4, 7} := by
    by_contra hv
    exact c12866 h u5_200 u12_40 hv
  have u19_23 : T {0, 4, 6} := by
    by_contra hv
    exact c28416 h u11_311 hv u13_41
  have u20_87 : T {3, 4, 6} := by
    by_contra hv
    exact c12868 h u5_200 u13_41 hv
  have u21_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c971 h hv u15_65
  have u22_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c656 h hv u16_44
  have u23_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16494 h hv u17_31 u6_95 n105
  have u24_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15638 h hv u17_31 u6_95 n105
  have u25_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c32741 h h0 hv n105
  have u26_52 : T {1, 4, 7} := by
    by_contra hv
    exact c12914 h u5_200 u13_41 u25_47 hv
  have u27_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12874 h u5_200 u25_47 hv
  have u28_68 : T {2, 3, 7} := by
    by_contra hv
    exact c12972 h u5_200 u25_47 hv u6_95
  have u29_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c28413 h u11_311 hv u26_52
  have u30_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c28527 h u11_311 u0_24 u26_52 hv
  have u31_260 : ¬ Q {1, 7, 8, 9} := by
    intro hv
    exact c21387 h hv u19_23 u27_72 u20_87
  have u32_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c20679 h hv u19_23 u27_72 u20_87
  have u33_13 : T {0, 2, 7} := by
    by_contra hv
    exact c28436 h u11_311 u14_10 u29_12 hv
  have u34_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20350 h hv u14_10 u15_65 u30_73
  have u35_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21192 h hv u14_10 u15_65 u30_73
  have u36_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19949 h hv u33_13 u28_68 u9_80
  have u37_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19099 h hv u33_13 u28_68 u9_80
  have u38_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c859 h hv u24_219 u2_234 u37_244 u34_253 u32_255 u10_256
  have u39_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c949 h hv u23_225 u1_240 u36_250 u10_256 u35_259 u31_260
  have u40_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c947 h hv u39_148 u23_225 u1_240 u36_250 u10_256 u35_259 u31_260
  have u41_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c857 h hv u38_142 u24_219 u2_234 u37_244 u34_253 u32_255 u10_256
  have u42_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c26450 h hv u29_12 u40_64
  have u43_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c27292 h hv u29_12 u41_58
  have u44_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c1309 h hv u22_228 u21_263 u42_297 u4_300 u43_303 u3_304
  exact c1307 h u18_88 u44_172 u22_228 u21_263 u42_297 u4_300 u43_303 u3_304

theorem c32743 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → False := by
  classical
  intro a116
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c31636 h h0 u0_105 a116

theorem c32744 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → False := by
  classical
  intro a311
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c32517 h h0 a311 u0_105

theorem c32745 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 8, 9} → False := by
  classical
  intro a291
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c32317 h h0 a291 u0_105

theorem c32746 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 8, 9} → False := by
  classical
  intro a256
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c32117 h h0 a256 u0_105

theorem c32747 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → False := by
  classical
  intro a200
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  exact c31917 h h0 a200 u0_105

theorem c32753 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 8} →
      ¬ Q {0, 3, 5, 8} → ¬ Q {0, 4, 5, 8} → False := by
  classical
  intro n198 n196 n141 n177 n187
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u2_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c426 h hv n141 n177 n187 n196 n198 u1_200
  exact c32585 h n198 u2_162 n141 u0_29 u1_200 n187 n196

theorem c32755 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → ¬ Q {1, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → False := by
  classical
  intro n280 n245 n300
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 n280 n300 hv u0_105
  exact c31555 h h0 u1_189 n300 n280 n245

theorem c32763 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 6, 7} → T {1, 4, 6} → T {2, 6, 7} → ¬ Q {2, 4, 6, 7} → False := by
  classical
  intro n300 a51 a80 n280
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u3_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u4_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u5_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32745 h h0 hv
  have u6_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 n280 n300 hv u0_105
  have u7_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 n280 hv n300
  have u8_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u6_189 hv
  have u9_31 : T {0, 6, 7} := by
    by_contra hv
    exact c459 h u6_189 hv
  have u10_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u6_189 u4_49 hv
  have u11_59 : T {1, 6, 7} := by
    by_contra hv
    exact c879 h u7_245 hv
  have u12_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c19175 h u7_245 hv u10_78
  have u13_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19177 h u7_245 u1_29 hv
  have u14_100 : T {3, 8, 9} := by
    by_contra hv
    exact c19272 h u7_245 u12_21 u13_70 hv
  have u15_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22475 h hv u8_23 a51 u0_105
  have u16_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27695 h hv u9_31 u11_59 a80
  have u17_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26839 h hv u9_31 u11_59 a80
  have u18_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9237 h hv u11_59 u10_78
  have u19_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21975 h hv u1_29 u11_59
  have u20_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c11325 h u6_189 hv u14_100
  have u21_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c19165 h u7_245 hv u14_100
  have u22_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1347 h hv u18_174 u2_230 u19_265 u17_299 u3_304 u16_305
  have u23_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c1337 h hv u18_174 u2_230 u19_265 u17_299 u22_302 u3_304 u16_305
  have u24_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c583 h hv u20_39
  have u25_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c163 h hv u21_11
  have u26_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25430 h hv u12_21 u4_49 u23_90
  have u27_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25150 h hv u12_21 u4_49 u23_90
  have u28_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c1165 h hv u25_162 u24_218 u15_268 u27_287 u26_289 u5_291
  exact c1157 h u10_78 u25_162 u24_218 u15_268 u28_278 u27_287 u26_289 u5_291

end BorsukNine.FiniteObstruction

end OAI
