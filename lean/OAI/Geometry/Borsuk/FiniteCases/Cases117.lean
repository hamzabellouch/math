import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases116

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32616 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 6, 7} → ¬ Q {3, 4, 6, 7} → ¬ Q {0, 4, 6, 7} → T {4, 6, 7} → False := by
  classical
  intro n280 n300 n189 a105
  have u0_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 n280 hv a105 n189
  exact c31556 h h0 u0_245 n300 n280 n189

private theorem c32617 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 6, 7} → T {1, 2, 6} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro n300 a40 n177 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32611 h h0 hv a40 n177 a49
  have u2_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u0_210 hv u1_105
  have u3_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u4_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u5_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32395 h h0 hv u4_43 a40
  have u6_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32506 h h0 hv u4_43 a40
  have u7_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c32615 h h0 hv u1_105 u6_309 u5_298 u3_311 n177 u0_210
  have u8_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv u7_24
  have u9_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u8_189 u1_105 u2_29
  have u10_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u11_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv n300 u8_189 u1_105
  have u12_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u11_280 hv u8_189 n300
  have u13_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c32216 h h0 u11_280 hv a49
  have u14_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c32016 h h0 hv u12_245 u10_70
  have u15_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c714 h hv u13_48
  have u16_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c1029 h hv u14_69
  have u17_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1392 h hv n177 u15_233 u16_268 u5_298 u6_309 u3_311
  exact c32591 h u16_268 u15_233 u9_93 u3_311 n177 u17_307 u5_298

private theorem c32618 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {1, 2, 5, 6} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 3, 6} → T {5, 6, 8} → ¬ T {5, 8, 9} → T {1, 2, 6} → ¬ Q {0, 1, 2, 9} → T {1, 3, 9} → False := by
  classical
  intro n222 n219 n216 n225 n221 n207 a112 n116 a40 n127 a49
  have u0_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u1_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c615 h hv u0_41
  have u2_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c611 h hv u0_41
  have u3_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u4_215 : Q {1, 2, 4, 9} := by
    by_contra hv
    exact c636 h u3_210 n127 hv n219 n222 u1_224 n225
  have u5_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c14967 h u4_215 hv a112
  have u6_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14544 h hv u5_19 n116
  have u7_124 : Q {0, 1, 2, 6} := by
    by_contra hv
    exact c31365 h n222 u2_220 n207 hv n221 u6_212 a40
  exact c589 h u7_124 n207 u6_212 n216 u2_220 n221 n222

private theorem c32620 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 3, 7} → Q {1, 2, 6, 9} → Q {3, 4, 6, 7} → T {5, 6, 8} → ¬ T {0, 4, 7} → ¬ Q {3, 4, 6, 9} → ¬ Q {0, 3, 4, 6} → ¬ T {0, 5, 8} → ¬ T {5, 8, 9} → T {1, 2, 9} → False := by
  classical
  intro n19 a222 a300 a112 n24 n302 n171 n29 n116 a43
  have u0_103 : T {4, 5, 8} := by
    by_contra hv
    exact c15946 h a222 n19 hv
  have u1_34 : T {0, 7, 8} := by
    by_contra hv
    exact c15988 h a222 n19 n24 hv
  have u2_28 : T {0, 5, 7} := by
    by_contra hv
    exact c15986 h a222 n19 n24 hv
  have u3_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31704 h h0 a112 u0_103 hv
  have u4_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26317 h hv u1_34 a43
  have u5_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c27017 h hv u2_28 a43
  have u6_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16746 h hv n29 u3_114 n116
  have u7_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21646 h hv n29 u3_114 n116
  exact c1302 h a300 n171 u6_227 u7_262 u4_296 u5_301 n302

theorem c32621 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 6} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 3, 5, 8} → T {1, 3, 9} → False := by
  classical
  intro a40 n127 n177 a49
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c32606 h h0 hv n177 a49
  have u1_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u2_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u3_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u2_210 hv
  have u4_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c32395 h h0 hv u3_43 a40
  have u5_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32506 h h0 hv u3_43 a40
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32611 h h0 hv a40 n177 a49
  have u7_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u6_105 hv
  have u8_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u2_210 hv u6_105
  have u9_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8804 h hv u1_41 u7_116
  have u10_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27158 h hv u8_29 u1_41
  have u11_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c32615 h h0 hv u6_105 u5_309 u4_298 u0_311 n177 u2_210
  have u12_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv u11_24
  have u13_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u2_210 u11_24 hv
  have u14_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13844 h hv u11_24 u7_116
  have u15_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u12_189 u6_105 u8_29
  have u16_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32617 h h0 hv a40 n177 a49
  have u17_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c32416 h h0 hv u16_300 u3_43
  have u18_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32415 h h0 hv u16_300 u3_43
  have u19_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c626 h hv u17_42
  have u20_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c630 h hv u17_42
  have u21_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c579 h hv u18_39
  have u22_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c585 h hv u18_39
  have u23_222 : Q {1, 2, 6, 9} := by
    by_contra hv
    exact c32618 h h0 hv u22_219 u21_216 u20_225 u19_221 u14_207 u13_112 u7_116 a40 n127 a49
  have u24_19 : T {0, 3, 7} := by
    by_contra hv
    exact c32620 h h0 hv u23_222 u16_300 u13_112 u11_24 u10_302 u9_171 u8_29 u7_116 u3_43
  have u25_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c15947 h u23_222 u24_19 hv
  have u26_118 : T {6, 7, 9} := by
    by_contra hv
    exact c31631 h h0 u25_103 hv
  have u27_31 : T {0, 6, 7} := by
    by_contra hv
    exact c14276 h u2_210 hv u25_103
  have u28_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17603 h hv u27_31 u6_105 u26_118
  have u29_268 : ¬ Q {2, 3, 5, 8} := by
    intro hv
    exact c22503 h hv u27_31 u6_105 u26_118
  have u30_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1392 h hv n177 u28_233 u29_268 u4_298 u5_309 u0_311
  exact c32591 h u29_268 u28_233 u15_93 u0_311 n177 u30_307 u4_298

theorem c32622 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 8, 9} → T {0, 3, 7} → ¬ T {0, 4, 7} → T {4, 6, 7} → ¬ Q {1, 2, 5, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {0, 1, 2, 9} → T {1, 3, 9} → False := by
  classical
  intro a225 a19 n24 a105 n216 n124 n127 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u0_210 n24 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u1_112
  have u3_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u0_210 hv a105
  have u4_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u5_93 : T {3, 5, 8} := by
    by_contra hv
    exact c32590 h h0 hv u4_189 a105 u3_29
  have u6_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u3_29
  have u7_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u8_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32601 h h0 hv a49
  have u9_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv u8_41
  have u10_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u11_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u12_42 : T {1, 2, 8} := by
    by_contra hv
    exact c630 h a225 hv
  have u13_64 : T {1, 8, 9} := by
    by_contra hv
    exact c950 h a225 hv
  have u14_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c16365 h a225 hv a105
  have u15_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c16369 h a225 a19 hv
  have u16_91 : T {3, 5, 6} := by
    by_contra hv
    exact c16374 h a225 n24 hv
  have u17_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32416 h h0 u12_42 hv u11_43
  have u18_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31627 h h0 u15_101 hv
  have u19_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1943 h hv u16_91 u18_120
  have u20_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u17_300 u4_189 a105
  have u21_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u20_280 hv u4_189 u17_300
  have u22_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c32216 h h0 u20_280 hv a49
  have u23_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c32215 h h0 hv u20_280 a49
  have u24_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24180 h u20_280 u3_29 hv u7_116
  have u25_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c24075 h u20_280 hv u24_57
  have u26_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c24153 h u20_280 a49 hv u13_64
  have u27_94 : T {3, 5, 9} := by
    by_contra hv
    exact c24156 h u20_280 u14_17 u23_45 hv
  have u28_20 : T {0, 3, 8} := by
    by_contra hv
    exact c24096 h u20_280 u14_17 hv u25_21
  have u29_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c32016 h h0 hv u21_245 u10_70
  have u30_78 : T {2, 5, 8} := by
    by_contra hv
    exact c19280 h u21_245 u3_29 hv u7_116
  have u31_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25196 h hv n24 u22_48
  have u32_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7266 h hv u22_48 u2_109
  have u33_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24353 h hv a19 u24_57
  have u34_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c866 h hv u26_58
  have u35_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2515 h hv u27_94 a105
  have u36_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c32033 h h0 u28_20 a19 hv
  have u37_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4326 h hv u29_69 u2_109
  have u38_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u24_57 u30_78 u5_93
  have u39_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31459 h h0 u33_282 u38_191 u36_247 hv
  have u40_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31377 h h0 u1_112 u32_160 u6_196 u37_139 u0_210 hv u34_253 u31_288 n216 u18_120
  have u41_123 : Q {0, 1, 2, 5} := by
    by_contra hv
    exact c31532 h h0 u19_122 u9_125 n124 n127 hv u35_126
  have u42_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31685 h h0 hv u2_109 u39_107
  have u43_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31737 h h0 hv u40_113 u39_107
  exact c2221 h u41_123 u42_110 u43_119 u18_120

theorem c32623 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 7} → T {4, 6, 7} → T {1, 3, 9} → False := by
  classical
  intro a219 n24 a105 a49
  have u0_210 : Q {1, 2, 3, 9} := by
    by_contra hv
    exact c31481 h h0 a49 hv
  have u1_112 : T {5, 6, 8} := by
    by_contra hv
    exact c14266 h u0_210 n24 hv
  have u2_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u1_112
  have u3_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u4_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c14275 h u0_210 hv a105
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u4_29
  have u6_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u7_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1040 h u0_210 hv
  have u8_43 : T {1, 2, 9} := by
    by_contra hv
    exact c635 h u0_210 hv
  have u9_39 : T {1, 2, 5} := by
    by_contra hv
    exact c585 h a219 hv
  have u10_58 : T {1, 5, 9} := by
    by_contra hv
    exact c860 h a219 hv
  have u11_96 : T {3, 6, 8} := by
    by_contra hv
    exact c15532 h a219 n24 hv
  have u12_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c15529 h a219 hv a105
  have u13_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c31819 h h0 u9_39 hv u8_43
  have u14_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c32536 h h0 hv u9_39 u8_43
  have u15_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c31930 h h0 hv u9_39 u8_43
  have u16_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32425 h h0 hv u9_39 u8_43
  have u17_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32415 h h0 u9_39 hv u8_43
  have u18_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c296 h hv u12_20
  have u19_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 hv u17_300 u3_189 a105
  have u20_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u19_280 hv u3_189 u17_300
  have u21_48 : ¬ T {1, 3, 8} := by
    intro hv
    exact c32216 h h0 u19_280 hv a49
  have u22_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c32215 h h0 hv u19_280 a49
  have u23_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24180 h u19_280 u4_29 hv u6_116
  have u24_64 : ¬ T {1, 8, 9} := by
    intro hv
    exact c24153 h u19_280 a49 u10_58 hv
  have u25_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c24135 h u19_280 hv u23_57 u10_58
  have u26_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c32015 h h0 hv u20_245 u7_70
  have u27_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c716 h hv u21_48
  have u28_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7964 h hv u22_45 u2_109
  have u29_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26038 h hv n24 u22_45
  have u30_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c958 h hv u24_64
  have u31_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22804 h hv u25_4 u2_109
  have u32_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5024 h hv u26_66 u2_109
  have u33_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c481 h hv u32_144 u28_165 u18_180 u13_190 u5_196 u15_201
  have u34_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c31621 h h0 hv u30_259 u33_203 u29_294
  have u35_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c31327 h u34_314 u18_180 u14_312 u11_96 u31_271 hv u27_236
  exact c1437 h u35_307 u18_180 u27_236 u31_271 u16_301 u14_312 u34_314

end BorsukNine.FiniteObstruction

end OAI
