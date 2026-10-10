import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases136

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32764 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 4, 6} → T {2, 6, 7} → ¬ Q {0, 5, 6, 8} → ¬ T {2, 4, 6} → False := by
  classical
  intro a51 a80 n196 n72
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u2_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u3_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u4_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12594 h hv u0_49 n72
  have u5_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u6_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32763 h h0 hv a51 a80 u5_280
  have u7_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u6_300 hv
  have u8_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h u6_300 hv
  have u9_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h u6_300 u3_29 hv
  have u10_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7635 h hv a51 u7_87 u1_105
  have u11_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4719 h hv a80 u8_95 u1_105
  have u12_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c31443 h hv u11_141 u3_29 u2_200 u10_162 u4_198 n196
  have u13_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c32585 h u4_198 u10_162 u11_141 u3_29 u2_200 hv n196
  have u14_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32599 h h0 u12_177 hv
  have u15_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c9651 h u12_177 a51 hv
  have u16_82 : T {2, 6, 9} := by
    by_contra hv
    exact c9730 h u12_177 u9_43 hv u15_84
  exact c11115 h u13_187 u14_40 a80 u16_82

private theorem c32765 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 6, 7} → ¬ Q {0, 5, 6, 8} → ¬ T {2, 4, 6} → False := by
  classical
  intro a80 n196 n72
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u4_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u5_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32745 h h0 hv
  have u6_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12594 h hv u4_49 n72
  have u7_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u8_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c32764 h h0 hv a80 n196 n72
  have u9_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv u8_51
  have u10_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c765 h hv u8_51
  have u11_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 u7_280 u9_245 hv
  have u12_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u7_280 u9_245 u0_105 hv
  have u13_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u11_300 hv
  have u14_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h u11_300 hv
  have u15_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h u11_300 u2_29 hv
  have u16_31 : T {0, 6, 7} := by
    by_contra hv
    exact c459 h u12_189 hv
  have u17_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u12_189 u4_49 hv
  have u18_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11328 h u12_189 u15_43 hv
  have u19_64 : T {1, 8, 9} := by
    by_contra hv
    exact c11376 h u12_189 u15_43 u4_49 hv
  have u20_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c11439 h u12_189 hv u17_78 u18_93
  have u21_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15483 h hv u1_24 u13_88 u0_105
  have u22_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u2_29 u14_95
  have u23_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19995 h hv u16_31 a80 u14_95
  have u24_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19139 h hv u16_31 a80 u14_95
  have u25_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c26869 h u11_300 hv u17_78
  have u26_138 : ¬ Q {0, 1, 4, 9} := by
    intro hv
    exact c4195 h hv u17_78 u14_95
  have u27_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19847 h hv u2_29 u17_78 u18_93
  have u28_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c11341 h u12_189 u19_64 hv
  have u29_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c26871 h u11_300 hv u19_64
  have u30_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c853 h hv u20_57
  have u31_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28128 h hv u25_8 n72
  have u32_54 : ¬ T {1, 4, 9} := by
    intro hv
    exact c797 h hv u26_138 u22_215 u3_230 u24_244 u10_247 u27_249 u23_250
  have u33_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c988 h hv u28_66
  have u34_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c163 h hv u29_11
  have u35_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c31598 h h0 hv u30_254 u6_198 u31_309
  have u36_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c25126 h hv u25_8 u4_49 u32_54
  have u37_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c1165 h hv u34_162 u21_218 u33_268 u36_287 u35_289 u5_291
  exact c1157 h u17_78 u34_162 u21_218 u33_268 u37_278 u36_287 u35_289 u5_291

private theorem c32766 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 6, 7} → ¬ Q {0, 5, 6, 8} → ¬ T {2, 4, 6} → False := by
  classical
  intro n245 n196 n72
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u3_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u4_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c32765 h h0 hv n196 n72
  have u5_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11054 h hv u1_49 u4_80
  have u6_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12594 h hv u1_49 n72
  have u7_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u8_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 u7_280 n245 hv
  have u9_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u7_280 n245 u0_105 hv
  have u10_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h u8_300 u3_29 hv
  have u11_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u9_189 u1_49 hv
  have u12_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11328 h u9_189 u10_43 hv
  have u13_64 : T {1, 8, 9} := by
    by_contra hv
    exact c11376 h u9_189 u10_43 u1_49 hv
  have u14_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c11439 h u9_189 hv u11_78 u12_93
  have u15_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c26871 h u8_300 hv u13_64
  have u16_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c843 h hv u14_57
  have u17_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c163 h hv u15_11
  exact c32585 h u6_198 u17_162 u16_141 u3_29 u2_200 u5_187 n196

private theorem c32767 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → T {1, 4, 6} → ¬ Q {0, 4, 5, 8} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 5, 7, 8} → False := by
  classical
  intro a300 a51 n187 n196 n198
  have u0_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u3_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h a300 hv
  have u4_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u5_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h a300 hv
  have u6_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7635 h hv a51 u3_87 u2_105
  have u7_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c32585 h n198 u6_162 hv u1_29 u0_200 n187 n196
  have u8_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c4725 h u7_141 u5_95 u2_105 hv
  have u9_99 : ¬ T {3, 7, 9} := by
    intro hv
    exact c4685 h u7_141 u4_88 u5_95 hv
  have u10_84 : T {2, 7, 9} := by
    by_contra hv
    exact c4736 h u7_141 hv u9_99 u8_118
  exact c4621 h u7_141 u10_84 u3_87

theorem c32768 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 6, 8} → ¬ T {2, 4, 6} → False := by
  classical
  intro n196 n72
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u4_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12594 h hv u1_49 n72
  have u5_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u6_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c32765 h h0 hv n196 n72
  have u7_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11054 h hv u1_49 u6_80
  have u8_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c32766 h h0 hv n196 n72
  have u9_51 : T {1, 4, 6} := by
    by_contra hv
    exact c761 h u8_245 hv
  have u10_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19177 h u8_245 u2_29 hv
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32767 h h0 hv u9_51 u7_187 n196 u4_198
  have u12_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 u5_280 u11_300 hv u0_105
  have u13_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u12_189 u1_49 hv
  have u14_94 : T {3, 5, 9} := by
    by_contra hv
    exact c11430 h u12_189 u1_49 u10_70 hv
  have u15_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c19279 h u8_245 u2_29 u13_78 hv
  have u16_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c19167 h u8_245 hv u14_94
  have u17_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c1383 h hv u15_93
  have u18_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c204 h hv u16_14
  have u19_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c31443 h u17_177 hv u2_29 u3_200 u18_162 u4_198 n196
  exact c424 h u19_141 u18_162 u17_177 u7_187 n196 u4_198 u3_200

theorem c32769 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 6, 7} → T {1, 4, 6} → ¬ T {2, 4, 6} → False := by
  classical
  intro n300 a51 n72
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c32745 h h0 hv
  have u4_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32768 h h0 hv n72
  have u5_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12594 h hv u2_49 n72
  have u6_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c1076 h hv n72
  have u7_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 u6_280 n300 hv u0_105
  have u8_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 u6_280 hv n300
  have u9_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c32763 h h0 n300 a51 hv u6_280
  have u10_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u7_189 hv
  have u11_31 : T {0, 6, 7} := by
    by_contra hv
    exact c459 h u7_189 hv
  have u12_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u7_189 u2_49 hv
  have u13_59 : T {1, 6, 7} := by
    by_contra hv
    exact c879 h u8_245 hv
  have u14_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19177 h u8_245 u1_29 hv
  have u15_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11054 h hv u2_49 u9_80
  have u16_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22475 h hv u10_23 a51 u0_105
  have u17_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c19279 h u8_245 u1_29 u12_78 hv
  have u18_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c19175 h u8_245 hv u12_78
  have u19_90 : T {3, 4, 9} := by
    by_contra hv
    exact c12410 h u4_196 u2_49 u14_70 hv
  have u20_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1389 h hv u17_93
  have u21_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c1393 h hv u17_93
  have u22_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20434 h hv u18_21 n72
  have u23_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18894 h hv u18_21 u9_80
  have u24_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7557 h hv u13_59 u19_90
  have u25_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c15397 h hv u11_31 u19_90
  have u26_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c31548 h h0 hv u23_243 u15_187 u20_298
  have u27_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c31598 h h0 hv u22_254 u5_198 u21_309
  have u28_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1167 h hv u24_162 u25_218 u16_268 u26_278 u27_289 u3_291
  exact c1157 h u12_78 u24_162 u25_218 u16_268 u26_278 u28_287 u27_289 u3_291

end BorsukNine.FiniteObstruction

end OAI
