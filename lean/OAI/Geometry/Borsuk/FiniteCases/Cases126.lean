import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases125

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32688 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n103 n280 a29 a154
  have u0_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u1_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u0_70
  have u2_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32684 h h0 hv n280 a29 a154
  have u3_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32687 h h0 hv u2_112 a29 a154
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c6434 h a154 u3_57 hv
  have u5_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 u1_245 u4_105 hv
  have u6_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c31815 h h0 u5_189 hv u0_70
  have u7_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c988 h hv u6_66
  have u8_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c31555 h h0 u5_189 hv n280 u1_245
  have u9_95 : T {3, 6, 7} := by
    by_contra hv
    exact c1419 h u8_300 hv
  have u10_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u4_105 hv
  have u11_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11442 h u5_189 u3_57 hv u10_116
  have u12_31 : T {0, 6, 7} := by
    by_contra hv
    exact c459 h u5_189 hv
  have u13_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14977 h hv u12_31 u11_93
  have u14_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32517 h h0 hv u4_105
  have u15_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c847 h hv u3_57
  have u16_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u17_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14689 h hv u16_21 u2_112
  have u18_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u2_112
  have u19_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u20_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u21_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv n103
  have u22_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 n103 hv
  have u23_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31707 h h0 u10_116 hv n103
  have u24_59 : T {1, 6, 7} := by
    by_contra hv
    exact c6436 h a154 hv n103
  have u25_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv a29 u22_118
  have u26_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1947 h hv u11_93 u22_118
  have u27_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14941 h hv u12_31 u9_95 u22_118
  have u28_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c14497 h hv u12_31 u9_95 u22_118
  have u29_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c32227 h h0 hv u23_114
  have u30_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv a29 u2_112 u23_114
  have u31_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7237 h hv u11_93 u2_112 u23_114
  have u32_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14549 h hv u16_21 u23_114
  have u33_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9763 h hv u24_59 u4_105 u22_118
  have u34_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c24895 h hv u12_31 u24_59 u9_95
  have u35_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c24039 h hv u12_31 u24_59 u9_95
  have u36_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c557 h hv u26_122 u25_205 u28_211 u32_212 u17_213 u27_214 u13_215
  have u37_75 : ¬ T {2, 4, 9} := by
    intro hv
    exact c1112 h hv u31_159 u13_215 u30_265 u35_279 u29_282 u19_284 u34_285
  have u38_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32591 h u7_268 u15_233 u11_93 u14_311 u33_177 hv u21_298
  have u39_26 : T {0, 4, 9} := by
    by_contra hv
    exact c27970 h u38_307 hv u37_75 u18_109
  have u40_35 : T {0, 7, 9} := by
    by_contra hv
    exact c27860 h u38_307 hv u36_38
  exact c27901 h u38_307 u20_15 u39_26 u40_35

theorem c32689 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n280 a29 a154
  have u0_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c32674 h h0 hv a29 a154
  have u1_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u2_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u1_70
  have u3_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u4_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u5_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32684 h h0 hv n280 a29 a154
  have u6_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14689 h hv u3_21 u5_112
  have u7_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32687 h h0 hv u5_112 a29 a154
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c843 h hv u7_57
  have u9_105 : T {4, 6, 7} := by
    by_contra hv
    exact c6434 h a154 u7_57 hv
  have u10_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u9_105 hv
  have u11_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u9_105
  have u12_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 u2_245 u9_105 hv
  have u13_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u12_189 hv
  have u14_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c31555 h h0 u12_189 hv n280 u2_245
  have u15_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11442 h u12_189 u7_57 hv u10_116
  have u16_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16233 h hv u13_23 u15_93
  have u17_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h u14_300 hv
  have u18_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c32412 h h0 u14_300 u4_15 hv
  have u19_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c163 h hv u18_11
  have u20_103 : T {4, 5, 8} := by
    by_contra hv
    exact c32688 h h0 hv n280 a29 a154
  have u21_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c32337 h h0 hv u20_103
  have u22_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31704 h h0 u5_112 u20_103 hv
  have u23_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c23351 h hv a29 u20_103 u5_112
  have u24_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8513 h hv u15_93 u20_103 u5_112
  have u25_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14083 h hv a29 u20_103 u5_112
  have u26_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15669 h hv u3_21 u20_103
  have u27_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2463 h hv u15_93 u20_103 u5_112
  have u28_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u22_114
  have u29_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u22_114
  have u30_51 : T {1, 4, 6} := by
    by_contra hv
    exact c6424 h a154 hv u22_114
  have u31_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9739 h hv u30_51 u9_105 u29_107
  have u32_223 : ¬ Q {1, 2, 7, 8} := by
    intro hv
    exact c16185 h hv u13_23 u17_87 u29_107
  have u33_217 : ¬ Q {1, 2, 5, 7} := by
    intro hv
    exact c15337 h hv u13_23 u17_87 u29_107
  have u34_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25579 h hv u13_23 u30_51 u17_87
  have u35_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c26287 h hv u13_23 u30_51 u17_87
  have u36_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31443 h u31_177 u8_141 a29 u11_200 u19_162 u28_198 hv
  have u37_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c602 h hv u27_125 u25_208 u6_213 u33_217 u26_220 u32_223 u16_224
  have u38_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c1247 h hv u24_168 u16_224 u23_274 u0_284 u34_290 u21_293 u35_295
  have u39_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c31886 h h0 hv u1_70 u36_196
  exact c12380 h u36_196 u37_41 u39_68 u38_84

private theorem c32690 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → T {5, 6, 8} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a103 a112 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u2_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c6427 h a154 hv a112
  have u3_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u4_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32689 h h0 hv a29 a154
  have u5_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u4_280 hv
  have u6_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32207 h h0 u4_280 hv
  have u7_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u8_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24075 h u4_280 u7_21 hv
  have u9_93 : T {3, 5, 8} := by
    by_contra hv
    exact c24184 h u4_280 u8_57 hv u6_116
  have u10_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5173 h hv u5_73 u9_93
  have u11_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15953 h hv u0_24 u9_93
  have u12_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c32212 h h0 u4_280 hv u7_21
  have u13_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c253 h hv u12_17
  have u14_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u15_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1567 h u4_280 hv
  have u16_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4609 h hv u14_70 u15_105
  have u17_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u15_105
  have u18_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c32137 h h0 hv a103
  have u19_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31704 h h0 a112 a103 hv
  have u20_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u19_114
  have u21_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u19_114
  have u22_51 : T {1, 4, 6} := by
    by_contra hv
    exact c6424 h a154 hv u19_114
  have u23_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7639 h hv u22_51 u15_105 u21_107
  have u24_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c31443 h u13_177 u16_141 a29 u17_200 u23_162 u20_198 hv
  have u25_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c31886 h h0 hv u14_70 u24_196
  have u26_88 : T {3, 4, 7} := by
    by_contra hv
    exact c12422 h u24_196 u2_52 hv u3_109
  have u27_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c432 h u24_196 u16_141 u23_162 u13_177 hv u20_198 u17_200
  have u28_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20399 h hv u0_24 u5_73 u26_88
  have u29_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21247 h hv u0_24 u5_73 u26_88
  have u30_61 : T {1, 6, 9} := by
    by_contra hv
    exact c11058 h u27_187 hv u25_68
  have u31_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c910 h hv u10_145 u11_222 u1_237 u28_253 u18_258 u29_259
  exact c902 h u30_61 u10_145 u11_222 u1_237 u31_247 u28_253 u18_258 u29_259

theorem c32691 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a112 a29 a154
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32689 h h0 hv a29 a154
  have u3_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u4_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c32213 h h0 u2_280 hv u3_21
  have u5_58 : T {1, 5, 9} := by
    by_contra hv
    exact c24072 h u2_280 u4_20 hv
  have u6_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c32212 h h0 u2_280 hv u3_21
  have u7_64 : T {1, 8, 9} := by
    by_contra hv
    exact c24070 h u2_280 u6_17 hv
  have u8_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c24151 h u2_280 hv u5_58 u7_64
  have u9_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32207 h h0 u2_280 hv
  have u10_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c24075 h u2_280 u3_21 hv
  have u11_93 : T {3, 5, 8} := by
    by_contra hv
    exact c24184 h u2_280 u10_57 hv u9_116
  have u12_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c253 h hv u6_17
  have u13_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1567 h u2_280 hv
  have u14_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32517 h h0 hv u13_105
  have u15_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u2_280 hv
  have u16_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17583 h hv u1_24 u15_73 u13_105
  have u17_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u18_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u17_70
  have u19_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u20_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32690 h h0 hv a112 a29 a154
  have u21_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1539 h hv u20_103
  have u22_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u20_103 hv
  have u23_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31707 h h0 u9_116 hv u20_103
  have u24_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7828 h hv u0_49 u20_103
  have u25_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10042 h hv u10_57 u20_103 u9_116
  have u26_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22784 h hv u10_57 u20_103 u9_116
  have u27_59 : T {1, 6, 7} := by
    by_contra hv
    exact c6436 h a154 hv u20_103
  have u28_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv a29 u22_118
  have u29_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31722 h h0 hv u13_105 u22_118
  have u30_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31724 h h0 hv u13_105 u22_118
  have u31_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv a29 a112 u23_114
  have u32_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22505 h hv u27_59 u13_105 u22_118
  have u33_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c1653 h hv u29_111
  have u34_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1659 h hv u29_111
  have u35_264 : ¬ Q {2, 3, 4, 8} := by
    intro hv
    exact c21828 h hv u8_8 u29_111
  have u36_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c1743 h hv u30_117
  have u37_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1749 h hv u30_117
  have u38_261 : ¬ Q {2, 3, 4, 5} := by
    intro hv
    exact c21408 h hv u8_8 u30_117
  have u39_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32591 h u32_268 u16_233 u11_93 u14_311 u12_177 hv u21_298
  have u40_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c27857 h u39_307 u1_24 hv
  have u41_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c32482 h h0 u39_307 u19_15 hv
  have u42_63 : T {1, 7, 9} := by
    by_contra hv
    exact c27928 h u39_307 u8_8 u40_43 hv
  have u43_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c140 h hv u41_10
  have u44_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28690 h hv u41_10 u10_57
  have u45_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17762 h hv u41_10 u9_116
  have u46_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21553 h hv a29 u42_63
  have u47_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c972 h hv u43_149 u28_205 u38_261 u46_262 u35_264 u31_265
  have u48_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c962 h hv u43_149 u28_205 u38_261 u46_262 u47_263 u35_264 u31_265
  have u49_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1420 h hv u25_179 u45_235 u26_270 u34_306 u37_312 u44_313
  have u50_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4882 h hv u48_65 u9_116
  have u51_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13160 h hv u10_57 u48_65
  have u52_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u2_280 u18_245 hv u49_300
  exact c460 h u52_189 u50_143 u24_164 u25_179 u33_195 u36_201 u51_202

end BorsukNine.FiniteObstruction

end OAI
