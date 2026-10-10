import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases123

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32670 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 5, 8} → ¬ T {0, 4, 7} → False := by
  classical
  intro n29 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c32668 h h0 hv n24
  have u4_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u2_105 u3_109
  have u5_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c1522 h hv u4_102
  have u6_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u2_105 u3_109
  have u7_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c1612 h hv u6_108
  have u8_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u9_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u8_193 u3_109 hv u0_304
  have u10_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u9_249 hv u8_193 u0_304
  have u11_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u3_109 hv
  have u12_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u2_105 hv
  have u13_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c350 h hv n24
  have u14_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 u1_49
  have u15_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14786 h hv n29 u11_112 u12_116
  have u16_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21786 h hv n29 u11_112 u12_116
  exact c1096 h u10_284 u13_157 u15_213 u16_263 u5_277 u14_280 u7_283

theorem c32671 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 4, 7} → False := by
  classical
  intro n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c360 h hv n24
  have u2_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32646 h h0 hv n24
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32660 h h0 hv n24
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u3_105 hv
  have u5_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u3_105
  have u6_109 : T {4, 7, 9} := by
    by_contra hv
    exact c32668 h h0 hv n24
  have u7_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u6_109 hv
  have u8_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u6_109
  have u9_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u1_193 u6_109 hv u0_304
  have u10_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u3_105 u6_109
  have u11_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u3_105 u6_109
  have u12_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u4_116 hv u7_112
  have u13_52 : T {1, 4, 7} := by
    by_contra hv
    exact c780 h u9_249 hv
  have u14_54 : T {1, 4, 9} := by
    by_contra hv
    exact c808 h u9_249 hv
  have u15_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c31574 h h0 u9_249 hv u1_193 u0_304
  have u16_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7647 h hv u13_52 u3_105 u6_109
  have u17_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h u15_284 hv
  have u18_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h u15_284 hv
  have u19_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4707 h hv u17_73 u3_105 u6_109
  have u20_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32670 h h0 hv n24
  have u21_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c19739 h u9_249 u20_29 hv
  have u22_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c24639 h u15_284 u20_29 hv
  have u23_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u2_177 u19_141 u20_29 u5_200 u16_162 hv u8_196
  have u24_154 : Q {0, 2, 3, 9} := by
    by_contra hv
    exact c32669 h h0 u20_29 hv n24
  have u25_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c434 h u23_198 u19_141 u16_162 u2_177 hv u8_196 u5_200
  have u26_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c12707 h u23_198 u14_54 u18_75 hv
  have u27_97 : T {3, 6, 9} := by
    by_contra hv
    exact c12684 h u23_198 u22_46 u21_67 hv
  have u28_87 : T {3, 4, 6} := by
    by_contra hv
    exact c12682 h u23_198 u22_46 u21_67 hv
  have u29_60 : T {1, 6, 8} := by
    by_contra hv
    exact c6438 h u24_154 hv u11_102
  have u30_55 : T {1, 5, 6} := by
    by_contra hv
    exact c6430 h u24_154 hv u10_108
  have u31_95 : T {3, 6, 7} := by
    by_contra hv
    exact c11134 h u25_187 u22_46 u21_67 hv
  have u32_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2368 h hv u26_90 u7_112
  have u33_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1955 h hv u27_97 u12_114
  have u34_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2543 h hv u28_87 u31_95 u27_97
  have u35_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2113 h hv u28_87 u31_95 u27_97
  have u36_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2645 h hv u28_87 u12_114
  have u37_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c24703 h u15_284 hv u30_55 u29_60
  have u38_124 : Q {0, 1, 2, 6} := by
    by_contra hv
    exact c31532 h h0 u33_122 u32_125 hv u36_127 u35_123 u34_126
  exact c63 h u38_124 u37_5

theorem c32672 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → ¬ Q {3, 6, 8, 9} → ¬ Q {3, 5, 6, 9} → ¬ Q {0, 3, 5, 8} → T {1, 4, 7} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 8} → ¬ T {1, 3, 6} → ¬ T {5, 6, 8} → T {4, 7, 9} → T {0, 5, 8} → T {2, 3, 9} → False := by
  classical
  intro a280 n314 n308 n177 a52 n196 n141 n46 n112 a109 a29 a70
  have u0_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u1_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c22959 h hv a29 a52
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1567 h a280 hv
  have u3_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32207 h h0 a280 hv
  have u4_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c31917 h h0 hv u2_105
  have u5_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7647 h hv a52 u2_105 a109
  have u6_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u3_116 hv n112
  have u7_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31705 h h0 u3_116 hv n112
  have u8_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h n177 n141 a29 u4_200 u5_162 hv n196
  have u9_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u6_114
  have u10_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c32537 h h0 hv u7_103
  have u11_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c31906 h h0 u8_198 hv a70
  have u12_97 : T {3, 6, 9} := by
    by_contra hv
    exact c12684 h u8_198 n46 u11_67 hv
  have u13_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c1444 h hv u0_237 u1_272 u9_302 n308 u10_313 n314
  exact c1442 h u12_97 u13_181 u0_237 u1_272 u9_302 n308 u10_313 n314

private theorem c32673 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ Q {2, 4, 6, 7} → Q {2, 4, 7, 9} → ¬ Q {1, 4, 6, 7} → Q {0, 2, 3, 9} → False := by
  classical
  intro n116 n280 a284 n245 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1627 h a284 hv
  have u3_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32247 h h0 a284 hv
  have u4_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv u3_112
  have u5_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22485 h hv u0_24 u4_52 u2_109
  have u6_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c32277 h h0 hv u2_109
  have u7_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u8_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u9_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h a284 hv
  have u10_243 : ¬ Q {1, 4, 5, 8} := by
    intro hv
    exact c18969 h hv u7_15 u8_70 u9_84
  have u11_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h a284 hv
  have u12_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20507 h hv u7_15 u8_70 u11_75
  have u13_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4657 h hv u8_70 u11_75 u9_84
  have u14_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h a284 hv
  have u15_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17585 h hv u0_24 u14_73 u2_109
  have u16_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u0_24 u8_70
  have u17_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u18_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c1730 h hv n116
  have u19_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c1732 h hv n116
  have u20_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv n116
  have u21_218 : ¬ Q {1, 2, 5, 8} := by
    intro hv
    exact c846 h hv u13_141 u15_233 u10_243 u16_252 u12_254 u18_256
  have u22_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c6435 h a154 hv u20_105
  have u23_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 n245 u20_105 hv
  have u24_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7647 h hv u4_52 u20_105 u2_109
  have u25_18 : T {0, 3, 6} := by
    by_contra hv
    exact c24632 h a284 hv u22_57
  have u26_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u23_189 u1_49 hv
  have u27_289 : ¬ Q {2, 5, 7, 8} := by
    intro hv
    exact c32303 h h0 u25_18 u17_21 hv
  have u28_278 : ¬ Q {2, 4, 5, 8} := by
    intro hv
    exact c32192 h h0 hv u25_18 u17_21
  exact c1157 h u26_78 u24_162 u21_218 u5_268 u28_278 u6_287 u27_289 u19_291

theorem c32674 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a284 a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c32642 h h0 hv
  have u2_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u3_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u4_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19177 h hv a29 u3_70
  have u5_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u6_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h a284 hv
  have u7_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1123 h a284 hv
  have u8_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h a284 hv
  have u9_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1627 h a284 hv
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32247 h h0 a284 hv
  have u11_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c24639 h a284 a29 hv
  have u12_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18005 h hv u0_24 u6_73 u9_109
  have u13_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27955 h hv u5_15 u7_75 u8_84
  have u14_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4657 h hv u3_70 u7_75 u8_84
  have u15_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12393 h hv u3_70 u7_75 u8_84
  have u16_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv u10_112
  have u17_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9745 h hv u16_52 u6_73 u9_109
  have u18_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22905 h hv u0_24 u16_52 u9_109
  have u19_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28527 h hv u0_24 u16_52 u6_73
  have u20_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28099 h hv u0_24 u16_52 u6_73
  have u21_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28947 h hv u0_24 u16_52 u6_73
  have u22_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10165 h hv u16_52 u6_73 u9_109
  have u23_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32672 h h0 hv u21_314 u20_308 u17_177 u16_52 u15_196 u14_141 u11_46 u10_112 u9_109 a29 u3_70
  have u24_116 : T {5, 8, 9} := by
    by_contra hv
    exact c32673 h h0 hv u23_280 a284 u4_245 a154
  have u25_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv u24_116
  have u26_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u25_105
  have u27_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c24747 h a284 a29 u26_57 hv
  have u28_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10219 h hv u26_57 u6_73
  have u29_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c24633 h a284 hv u26_57
  have u30_5 : T {0, 1, 6} := by
    by_contra hv
    exact c24626 h a284 hv u27_93
  have u31_96 : T {3, 6, 8} := by
    by_contra hv
    exact c24724 h a284 u29_18 u11_46 hv
  have u32_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c32248 h h0 hv a284 u30_5
  have u33_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c32250 h h0 hv a284 u30_5
  have u34_312 : Q {3, 6, 7, 8} := by
    by_contra hv
    exact c31327 h u21_314 u22_180 hv u31_96 u18_271 u13_307 u12_236
  have u35_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22528 h hv u33_7 u25_105
  have u36_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h u34_312 hv
  have u37_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 u34_312 hv
  have u38_301 : Q {3, 4, 6, 8} := by
    by_contra hv
    exact c1439 h u34_312 u22_180 u12_236 u18_271 hv u13_307 u21_314
  have u39_50 : ¬ T {1, 4, 5} := by
    intro hv
    exact c28555 h u34_312 u5_15 hv
  have u40_39 : T {1, 2, 5} := by
    by_contra hv
    exact c28618 h u34_312 u32_4 hv u39_50
  have u41_79 : ¬ T {2, 5, 9} := by
    intro hv
    exact c28655 h u34_312 u5_15 u7_75 hv
  have u42_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u36_117
  have u43_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9223 h hv u40_39 u36_117
  have u44_58 : T {1, 5, 9} := by
    by_contra hv
    exact c28680 h u34_312 hv u41_79 u37_104
  have u45_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1584 h u38_301 hv
  have u46_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c27013 h u38_301 hv u44_58
  have u47_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32424 h h0 u38_301 u40_39 hv
  have u48_77 : T {2, 5, 7} := by
    by_contra hv
    exact c27102 h u38_301 u46_13 u47_41 hv
  have u49_71 : T {2, 4, 5} := by
    by_contra hv
    exact c28664 h u34_312 u39_50 hv u37_104
  have u50_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10485 h hv u40_39 u45_106
  have u51_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u45_106
  have u52_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10693 h hv u40_39 u49_71 u48_77
  have u53_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c1399 h hv u1_234 u35_269 u42_299 u20_308 u51_310 u19_311
  exact c306 h a154 u2_133 u43_174 u53_178 u28_181 u50_183 u52_184

end BorsukNine.FiniteObstruction

end OAI
