import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases132

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32725 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 4} → ¬ Q {0, 1, 7, 8} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 3, 5, 6} → ¬ Q {3, 6, 8, 9} → ¬ T {4, 7, 8} → Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → False := by
  classical
  intro a38 n146 n272 n266 n314 n108 a306 a312
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u3_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h a306 hv
  have u4_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 n108 hv
  have u5_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31690 h h0 hv u4_113 u3_111
  have u6_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8248 h hv u0_49 u5_101
  have u7_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u8_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u9_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u7_104 u8_110 hv
  have u10_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 u9_107 hv
  have u11_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31745 h h0 n108 hv u10_114
  have u12_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32367 h h0 hv u11_120
  have u13_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv n108
  have u14_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31897 h h0 hv u9_107
  have u15_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u8_110 u7_104 hv
  have u16_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u15_109
  have u17_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h a312 hv
  have u18_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31726 h h0 u3_111 u17_117 hv
  have u19_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c1764 h hv u18_118
  have u20_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1361 h a306 hv
  have u21_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c13425 h hv a38 u20_91
  have u22_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9363 h hv a38 u11_120
  have u23_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c27721 h a306 hv a38
  have u24_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32534 h h0 a312 hv a38
  have u25_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10343 h hv a38 u4_113
  have u26_85 : T {2, 8, 9} := by
    by_contra hv
    exact c27838 h a306 u23_36 hv u8_110
  have u27_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10204 h hv u24_39 n108
  have u28_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c509 h hv n146 u6_167 u25_182 u13_192 u14_198 u21_204
  have u29_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17211 h hv u1_24 u26_85
  have u30_34 : ¬ T {0, 7, 8} := by
    intro hv
    exact c31373 h h0 u21_204 u14_198 u13_192 hv u28_201 n146
  have u31_308 : Q {3, 5, 6, 9} := by
    by_contra hv
    exact c1362 h a306 u22_175 u29_231 n266 u12_296 u16_307 hv
  have u32_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27160 h hv u30_34 u24_39
  exact c1452 h u31_308 u27_181 u2_237 n272 u32_302 u19_313 n314

private theorem c32726 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro a306 a312 n179 n270 a95 n105
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u4_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u5_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h a312 hv
  have u6_98 : T {3, 7, 8} := by
    by_contra hv
    exact c1468 h a312 hv
  have u7_96 : T {3, 6, 8} := by
    by_contra hv
    exact c1438 h a312 hv
  have u8_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u9_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1951 h hv a95 u8_116
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u2_24 u8_116
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u12_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1361 h a306 hv
  have u13_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h a306 hv
  have u14_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u15_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7197 h hv u12_91 a95 u7_96
  have u16_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u14_110 u4_104 hv
  have u17_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u4_104 u14_110 hv
  have u18_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u16_109 hv
  have u19_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u16_109
  have u20_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 u17_107 hv
  have u21_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13993 h hv u0_29 u17_107
  have u22_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u1_49 u18_112
  have u23_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6708 h hv u1_49 u20_114
  have u24_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c32724 h h0 hv u15_159 a306 a312 n179 u9_122 n105
  have u25_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u24_108 hv
  have u26_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31663 h h0 hv u24_108 n105
  have u27_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31745 h h0 u24_108 hv u20_114
  have u28_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31718 h h0 u25_113 hv u8_116
  have u29_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14127 h hv u2_24 u25_113
  have u30_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7081 h hv u12_91 u13_111 u25_113
  have u31_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u26_102
  have u32_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22907 h hv u2_24 u26_102 u16_109
  have u33_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18007 h hv u2_24 u26_102 u16_109
  have u34_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32367 h h0 hv u27_120
  have u35_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6685 h hv u6_98 u5_117 u27_120
  have u36_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u22_157 u30_158 u15_159 hv u23_156 u9_122 u35_155
  have u37_64 : T {1, 8, 9} := by
    by_contra hv
    exact c27710 h a306 u36_10 hv
  have u38_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22111 h hv u2_24 u37_64
  have u39_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6021 h hv u37_64 u26_102
  have u40_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21681 h hv u37_64 u8_116 u27_120
  have u41_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8939 h hv u37_64 u8_116 u27_120
  have u42_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c1006 h hv u39_151 u10_207 u40_262 u38_266 n270 u32_271
  have u43_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c992 h hv u39_151 u10_207 u40_262 u38_266 n270 u32_271 u42_272
  have u44_146 : ¬ Q {0, 1, 7, 8} := by
    intro hv
    exact c5306 h hv u43_67 u4_104
  have u45_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c32725 h h0 hv u44_146 u42_272 u38_266 u31_314 u24_108 a306 a312
  have u46_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv u45_38
  have u47_36 : T {0, 8, 9} := by
    by_contra hv
    exact c27720 h a306 hv u45_38
  have u48_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv u45_38 u28_115
  have u49_206 : Q {1, 2, 3, 5} := by
    by_contra hv
    exact c31535 h h0 hv u29_209 u3_210 u10_207 u21_208 u46_205
  have u50_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16779 h hv u47_36 u8_116 u27_120
  have u51_301 : Q {3, 4, 6, 8} := by
    by_contra hv
    exact c1439 h a312 u48_180 u33_236 u32_271 hv u19_307 u31_314
  have u52_39 : T {1, 2, 5} := by
    by_contra hv
    exact c575 h u49_206 hv
  have u53_26 : ¬ T {0, 4, 9} := by
    intro hv
    exact c13709 h u49_206 hv u5_117
  have u54_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1304 h u51_301 u41_171 u50_227 u40_262 u34_296 u11_300 hv
  have u55_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c32435 h h0 u52_39 hv u54_302
  exact c27718 h a306 u53_26 u55_42

private theorem c32727 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → T {0, 5, 9} → T {4, 5, 6} → Q {3, 6, 7, 9} → T {5, 8, 9} → False := by
  classical
  intro n108 a30 a101 a313 a116
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u4_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u5_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c32557 h h0 hv a101
  have u6_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31628 h h0 a101 hv
  have u7_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u8_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv u0_29 u7_118
  have u9_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h a313 u0_29 hv
  have u10_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 a313 hv
  have u11_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u1_24 a116
  have u12_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 n108 hv
  have u13_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31671 h h0 hv n108 u10_103
  have u14_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31692 h h0 u12_113 hv a101
  have u15_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14127 h hv u1_24 u12_113
  have u16_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14095 h hv a30 u12_113 a116
  have u17_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u13_106
  have u18_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10482 h hv u9_38 u14_112
  have u19_206 : Q {1, 2, 3, 5} := by
    by_contra hv
    exact c31535 h h0 hv u15_209 u2_210 u11_207 u16_208 u8_205
  have u20_274 : Q {2, 3, 7, 9} := by
    by_contra hv
    exact c1484 h a313 u18_183 u4_239 hv u3_304 u17_310 u5_315
  have u21_23 : T {0, 4, 6} := by
    by_contra hv
    exact c13702 h u19_206 hv u6_120
  have u22_57 : T {1, 5, 8} := by
    by_contra hv
    exact c23352 h u20_274 hv u10_103 u14_112
  exact c23233 h u20_274 u21_23 u22_57

theorem c32728 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 3, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro n235 n179 n270 a95 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u3_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u4_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u5_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u4_29 a95
  have u6_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv u0_49 n105
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u9_312 : Q {3, 6, 7, 8} := by
    by_contra hv
    exact c32722 h h0 hv n235 n179 n270 a95 n105
  have u10_96 : T {3, 6, 8} := by
    by_contra hv
    exact c1438 h u9_312 hv
  have u11_98 : T {3, 7, 8} := by
    by_contra hv
    exact c1468 h u9_312 hv
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h u9_312 hv
  have u13_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 u9_312 hv
  have u14_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15533 h hv u1_24 u10_96
  have u15_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c32726 h h0 hv u9_312 n179 n270 a95 n105
  have u16_313 : Q {3, 6, 7, 9} := by
    by_contra hv
    exact c1424 h u9_312 n179 n235 n270 u8_300 u15_306 hv
  have u17_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1453 h u16_313 hv
  have u18_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h u16_313 hv
  have u19_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 u16_313 hv
  have u20_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h u16_313 u4_29 hv
  have u21_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31787 h h0 hv u18_118
  have u22_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31651 h h0 u13_104 hv u19_103
  have u23_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31653 h h0 hv u13_104 u19_103
  have u24_30 : T {0, 5, 9} := by
    by_contra hv
    exact c28560 h u9_312 hv u20_38
  have u25_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2661 h hv u11_98 u22_101
  have u26_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u23_102 hv
  have u27_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u23_102
  have u28_108 : T {4, 7, 8} := by
    by_contra hv
    exact c32727 h h0 hv u24_30 u22_101 u16_313 u7_116
  have u29_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u28_108 hv
  have u30_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv u28_108
  have u31_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31744 h h0 u12_117 u28_108 hv
  have u32_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16047 h hv u1_24 u23_102 u28_108
  have u33_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23047 h hv u1_24 u23_102 u28_108
  have u34_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31737 h h0 u26_119 u29_113 hv
  have u35_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u31_114
  have u36_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10202 h hv u20_38 u31_114
  have u37_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1454 h u16_313 u36_181 u2_237 u33_272 hv u30_308 u27_314
  have u38_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4733 h hv u17_97 u34_107 u18_118
  have u39_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1305 h u37_302 hv
  have u40_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c27159 h u37_302 u4_29 hv
  have u41_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16239 h hv u4_29 u39_87
  have u42_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c646 h hv u25_127 u3_210 u5_215 u14_219 u32_222 u41_224
  have u43_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c31390 h u32_222 hv u42_225 u41_224 u5_215 u3_210 u14_219
  have u44_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9648 h hv u43_43 n105
  have u45_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12328 h hv u20_38 u40_41 u43_43
  exact c32648 h u38_141 u21_187 u45_196 u35_198 u4_29 u44_177 u6_162

end BorsukNine.FiniteObstruction

end OAI
