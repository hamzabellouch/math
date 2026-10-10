import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases134

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32736 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro a311 n200 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c32733 h h0 hv n105
  have u4_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c32729 h h0 hv n105
  have u5_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u6_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c32730 h h0 n200 hv u5_116
  have u7_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32728 h h0 u4_235 u6_179 u3_270 hv n105
  have u8_31 : T {0, 6, 7} := by
    by_contra hv
    exact c32584 h h0 hv u7_95 n105 n200
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c28419 h a311 u1_24 hv
  have u11_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28421 h a311 u8_31 hv
  have u12_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c28459 h a311 hv u1_24 u8_31
  have u13_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c28461 h a311 hv u1_24 u8_31
  have u14_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32599 h h0 hv u10_40
  have u15_41 : T {1, 2, 7} := by
    by_contra hv
    exact c28468 h a311 u11_38 u10_40 hv
  have u16_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28408 h a311 u12_6 hv
  have u17_51 : T {1, 4, 6} := by
    by_contra hv
    exact c28414 h a311 u13_13 hv
  have u18_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c28417 h a311 hv u15_41
  have u19_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32735 h h0 hv a311 n200 n105
  have u20_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 hv n200 u19_256 a311
  have u21_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c25619 h u20_291 u1_24 hv
  have u22_87 : T {3, 4, 6} := by
    by_contra hv
    exact c25708 h u20_291 u21_46 hv u7_95
  have u23_59 : T {1, 6, 7} := by
    by_contra hv
    exact c25740 h u20_291 hv u7_95 n105
  have u24_18 : T {0, 3, 6} := by
    by_contra hv
    exact c25704 h u20_291 hv u21_46 u7_95
  have u25_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c25621 h u20_291 u8_31 hv
  have u26_47 : T {1, 3, 7} := by
    by_contra hv
    exact c25616 h u20_291 u18_23 hv
  have u27_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c25613 h u20_291 u24_18 hv
  have u28_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12699 h hv u17_51 u16_72 u22_87
  have u29_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11087 h hv u15_41 u26_47 u23_59
  have u30_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12338 h hv u11_38 u25_44 u27_52
  have u31_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c32585 h u28_198 u9_162 hv u2_29 n200 u29_187 u30_196
  exact c424 h u31_141 u9_162 u14_177 u29_187 u30_196 u28_198 n200

theorem c32737 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 8, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n200 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c32733 h h0 hv n105
  have u4_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c32729 h h0 hv n105
  have u5_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u1_49 n105
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u7_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c32730 h h0 n200 hv u6_116
  have u8_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32728 h h0 u4_235 u7_179 u3_270 hv n105
  have u9_31 : T {0, 6, 7} := by
    by_contra hv
    exact c32584 h h0 hv u8_95 n105 n200
  have u10_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32736 h h0 hv n200 n105
  have u11_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 u6_116 n200 u10_311 hv
  have u12_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c32697 h h0 u10_311 hv u6_116 n200
  have u13_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c25619 h u11_291 u0_24 hv
  have u14_18 : T {0, 3, 6} := by
    by_contra hv
    exact c25704 h u11_291 hv u13_46 u8_95
  have u15_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c25621 h u11_291 u9_31 hv
  have u16_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c25613 h u11_291 u14_18 hv
  have u17_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c20719 h u12_256 u0_24 hv
  have u18_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c20713 h u12_256 u14_18 hv
  have u19_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12616 h hv u15_44 u13_46 u1_49
  have u20_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11134 h hv u13_46 u17_67 u8_95
  have u21_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12314 h hv u1_49 u18_73
  have u22_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9742 h hv u16_52 u18_73 n105
  have u23_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c32585 h u19_198 u5_162 hv u2_29 n200 u20_187 u21_196
  exact c424 h u23_141 u5_162 u22_177 u20_187 u21_196 u19_198 n200

theorem c32738 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 8, 9} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a256 n95 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u3_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u4_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32737 h h0 hv n105
  have u6_59 : T {1, 6, 7} := by
    by_contra hv
    exact c12998 h u5_200 hv n95 n105
  have u7_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c12881 h u5_200 u6_59 hv
  have u8_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c969 h hv u7_65
  have u9_38 : T {1, 2, 4} := by
    by_contra hv
    exact c12864 h u5_200 hv n95
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31918 h h0 u5_200 hv u9_38
  have u11_88 : T {3, 4, 7} := by
    by_contra hv
    exact c12866 h u5_200 u10_40 hv
  have u12_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c592 h hv u10_40
  have u13_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21975 h hv u1_29 u6_59
  have u14_80 : T {2, 6, 7} := by
    by_contra hv
    exact c13000 h u5_200 hv n95 n105
  have u15_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1425 h hv n95
  have u16_57 : T {1, 5, 8} := by
    by_contra hv
    exact c855 h a256 hv
  have u17_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c20719 h a256 u0_24 hv
  have u18_10 : T {0, 2, 4} := by
    by_contra hv
    exact c20704 h a256 hv n95
  have u19_18 : T {0, 3, 6} := by
    by_contra hv
    exact c20804 h a256 hv u17_67 n95
  have u20_31 : T {0, 6, 7} := by
    by_contra hv
    exact c20838 h a256 hv n95 n105
  have u21_68 : T {2, 3, 7} := by
    by_contra hv
    exact c20768 h a256 u7_65 u17_67 hv
  have u22_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c20707 h a256 hv u11_88
  have u23_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9235 h hv u16_57 u14_80
  have u24_72 : T {2, 4, 6} := by
    by_contra hv
    exact c12938 h u5_200 u10_40 u17_67 hv
  have u25_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28355 h hv u18_10 u9_38 u24_72
  have u26_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c29057 h hv u18_10 u9_38 u24_72
  have u27_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c32123 h h0 hv u19_18 a256
  have u28_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27695 h hv u20_31 u6_59 u14_80
  have u29_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26839 h hv u20_31 u6_59 u14_80
  have u30_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c19459 h hv u1_29 u21_68
  have u31_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11619 h hv u16_57 u21_68
  have u32_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c12971 h u5_200 hv u21_68 u11_88
  have u33_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c172 h hv u22_12
  have u34_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1347 h hv u23_174 u2_230 u13_265 u29_299 u3_304 u28_305
  have u35_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10499 h hv u16_57 u24_72
  have u36_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c1478 h hv u35_183 u4_239 u3_304 u25_310 u15_313 u26_315
  have u37_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c31288 h u25_310 u35_183 u26_315 u36_274 u15_313 hv u4_239
  have u38_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c31565 h h0 hv u30_247 u34_302 u31_191
  have u39_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24304 h hv u27_19 u32_47 u37_99
  have u40_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23596 h hv u27_19 u32_47 u37_99
  exact c31226 h u39_281 u38_282 u33_156 u24_72 u40_276 u12_212 u8_262

theorem c32739 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 6, 7} → ¬ Q {3, 5, 8, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n95 n311 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u4_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c32737 h h0 hv n105
  have u6_38 : T {1, 2, 4} := by
    by_contra hv
    exact c12864 h u5_200 hv n95
  have u7_59 : T {1, 6, 7} := by
    by_contra hv
    exact c12998 h u5_200 hv n95 n105
  have u8_80 : T {2, 6, 7} := by
    by_contra hv
    exact c13000 h u5_200 hv n95 n105
  have u9_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c31918 h h0 u5_200 hv u6_38
  have u10_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c21975 h hv u2_29 u7_59
  have u11_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c12871 h u5_200 hv u8_80
  have u12_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c32738 h h0 hv n95 n105
  have u13_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31604 h h0 u5_200 hv u12_256 n311
  have u14_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1170 h u13_291 hv
  have u15_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c25619 h u13_291 u0_24 hv
  have u16_3 : T {0, 1, 4} := by
    by_contra hv
    exact c25604 h u13_291 hv n95
  have u17_31 : T {0, 6, 7} := by
    by_contra hv
    exact c25738 h u13_291 hv n95 n105
  have u18_47 : T {1, 3, 7} := by
    by_contra hv
    exact c25668 h u13_291 u11_44 u15_46 hv
  have u19_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9237 h hv u7_59 u14_78
  have u20_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12906 h u5_200 u9_40 u15_46 hv
  have u21_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c25388 h hv u11_44 u15_46 u1_49
  have u22_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12616 h hv u11_44 u15_46 u1_49
  have u23_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28191 h hv u16_3 u6_38 u20_51
  have u24_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27695 h hv u17_31 u7_59 u8_80
  have u25_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26839 h hv u17_31 u7_59 u8_80
  have u26_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24359 h hv u2_29 u18_47
  have u27_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11613 h hv u18_47 u14_78
  have u28_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c1347 h hv u19_174 u3_230 u10_265 u25_299 u4_304 u24_305
  have u29_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31450 h h0 u23_309 hv u22_198 u21_289
  have u30_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c31564 h h0 u28_302 hv u26_282 u27_191
  have u31_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31459 h h0 u26_282 u27_191 u30_247 hv
  exact c31639 h h0 u31_107 u29_114

theorem c32740 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a95 n105
  have u0_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c32733 h h0 hv n105
  have u1_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c32729 h h0 hv n105
  have u2_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u3_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c32732 h h0 hv a95 u2_116
  exact c32728 h h0 u1_235 u3_179 u0_270 a95 n105

end BorsukNine.FiniteObstruction

end OAI
