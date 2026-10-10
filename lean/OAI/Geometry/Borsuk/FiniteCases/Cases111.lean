import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases110

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32574 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {3, 6, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a117 a95 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u2_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u1_116
  have u3_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u2_105 u0_109
  have u4_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31629 h h0 u3_102 hv
  have u5_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u2_105 u0_109
  have u6_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u5_108 hv
  have u7_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u8_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u1_116 hv u7_112
  have u9_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u8_114
  have u10_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c729 h hv n49
  have u11_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c723 h hv n49
  have u12_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u0_109
  have u13_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv a117
  have u14_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31720 h h0 a117 hv u2_105
  have u15_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31750 h h0 a117 hv u8_114
  have u16_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u13_104 hv u9_107
  have u17_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31649 h h0 hv u3_102 u13_104
  have u18_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1659 h hv u14_111
  have u19_174 : Q {0, 3, 4, 9} := by
    by_contra hv
    exact c32573 h h0 hv a117 a95 n49 a304
  have u20_26 : T {0, 4, 9} := by
    by_contra hv
    exact c382 h u19_174 hv
  have u21_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c9223 h u19_174 hv a117
  have u22_41 : T {1, 2, 7} := by
    by_contra hv
    exact c9226 h u19_174 hv u7_112
  have u23_42 : T {1, 2, 8} := by
    by_contra hv
    exact c9228 h u19_174 hv u14_111
  have u24_55 : T {1, 5, 6} := by
    by_contra hv
    exact c9318 h u19_174 hv u14_111 u7_112
  have u25_76 : T {2, 5, 6} := by
    by_contra hv
    exact c9320 h u19_174 hv u14_111 u7_112
  have u26_83 : ¬ T {2, 7, 8} := by
    intro hv
    exact c9361 h u19_174 hv u8_114 a117
  have u27_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22215 h hv u20_26 u0_109 u16_110
  have u28_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17315 h hv u20_26 u0_109 u16_110
  have u29_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13791 h hv u20_26 u0_109 u16_110
  have u30_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u21_39
  have u31_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9365 h hv u22_41 u16_110
  have u32_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c27437 h a304 hv u23_42
  have u33_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c32374 h h0 u22_41 hv u23_42
  have u34_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32496 h h0 hv u22_41 u23_42
  have u35_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c27435 h a304 hv u24_55
  have u36_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3351 h hv u25_76 u0_109
  have u37_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3297 h hv u25_76 u17_101 u6_113
  have u38_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c2936 h hv u26_83 u9_107
  have u39_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3180 h hv u26_83 u5_108 u15_120
  have u40_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16607 h hv u30_32 a117 u4_119
  have u41_91 : ¬ T {3, 5, 6} := by
    intro hv
    exact c1352 h hv u31_175 u28_231 u27_266 u33_296 u18_306 u12_307 u34_308
  have u42_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17346 h hv u35_14 u9_107
  have u43_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c674 h hv u38_129 u29_206 u40_226 u28_231 u42_232 u10_234
  have u44_128 : Q {0, 1, 3, 4} := by
    by_contra hv
    exact c31533 h h0 u38_129 u36_132 hv u11_133 u37_131 u39_130
  have u45_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c31320 h u28_231 u42_232 u10_234 hv u29_206 u43_233 u40_226
  have u46_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19842 h hv u32_27 u41_91 u7_112
  have u47_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24742 h hv u32_27 u41_91 u7_112
  have u48_80 : T {2, 6, 7} := by
    by_contra hv
    exact c2790 h u44_128 hv u1_116
  have u49_81 : ¬ T {2, 6, 8} := by
    intro hv
    exact c2811 h u44_128 u25_76 u48_80 hv
  have u50_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11890 h hv u45_45 u49_81
  exact c31576 h h0 u46_249 u47_284 a304 u50_193

private theorem c32575 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 4, 9} → ¬ T {6, 7, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a174 n117 n49 a304
  have u0_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u1_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31727 h h0 hv n117 u0_112
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u3_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u2_29 hv
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u5_116
  have u7_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u6_105 u4_109
  have u8_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10626 h hv u3_40 u7_102
  have u9_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u6_105 u4_109
  have u10_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9784 h hv u3_40 u9_108
  have u11_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c723 h hv n49
  have u12_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u13_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u12_118
  have u14_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u15_21 : T {0, 3, 9} := by
    by_contra hv
    exact c307 h a174 hv
  have u16_39 : T {1, 2, 5} := by
    by_contra hv
    exact c9222 h a174 hv n117
  have u17_41 : T {1, 2, 7} := by
    by_contra hv
    exact c9226 h a174 hv u0_112
  have u18_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11465 h hv u16_39 u14_99
  have u19_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10485 h hv u16_39 u1_106
  have u20_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32424 h h0 hv u16_39 u17_41
  have u21_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10207 h hv u17_41 u13_103
  have u22_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 hv u1_106 u20_301 u18_190
  have u23_154 : Q {0, 2, 3, 9} := by
    by_contra hv
    exact c308 h a174 u11_133 hv u10_178 u21_181 u19_183 u8_184
  have u24_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19413 h u22_246 u15_21 hv u14_99
  exact c1038 h u23_154 u24_70

private theorem c32576 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → T {1, 2, 7} → ¬ T {6, 7, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a39 a41 n117 n49 a304
  have u0_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u1_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u0_118
  have u2_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10207 h hv a41 u1_103
  have u3_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c32575 h h0 hv n117 n49 a304
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u5_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31727 h h0 hv n117 u4_112
  have u6_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u5_106
  have u7_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31725 h h0 n117 hv u0_118
  have u8_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32457 h h0 hv u7_111
  have u9_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u9_29 hv
  have u11_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u12_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u13_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u12_116
  have u14_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u13_105 u11_109
  have u15_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9784 h hv u10_40 u14_108
  have u16_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u12_116 hv u4_112
  have u17_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23071 h hv u9_29 u1_103 u16_114
  have u18_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u16_114
  have u19_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv u12_116
  have u20_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c731 h hv n49
  have u21_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c729 h hv n49
  have u22_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u23_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c31513 h h0 hv a304
  have u24_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u25_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11465 h hv a39 u24_99
  have u26_32 : ¬ T {0, 6, 8} := by
    intro hv
    exact c27441 h a304 hv a39
  have u27_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c32424 h h0 hv a39 a41
  have u28_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32556 h h0 hv a41 a39
  have u29_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 hv u5_106 u27_301 u25_190
  have u30_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22090 h hv u26_32 u4_112 n117
  have u31_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c1452 h hv u2_181 u20_237 u17_272 u18_302 u23_313 u28_314
  have u32_51 : T {1, 4, 6} := by
    by_contra hv
    exact c763 h u29_246 hv
  have u33_299 : Q {3, 4, 5, 9} := by
    by_contra hv
    exact c1349 h a304 u3_174 u22_230 u30_265 hv u18_302 u8_305
  have u34_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22621 h hv u32_51 u13_105 u5_106
  exact c1405 h u33_299 u15_178 u21_234 u34_269 u31_308 u6_310 u19_311

theorem c32577 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → ¬ T {6, 7, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a41 n117 n49 a304
  have u0_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c32575 h h0 hv n117 n49 a304
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u2_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u1_29 hv
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u5_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u4_116
  have u6_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u5_105 u3_109
  have u7_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u6_108 hv
  have u8_104 : T {4, 5, 9} := by
    by_contra hv
    exact c31633 h h0 hv n117
  have u9_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31712 h h0 hv u8_104 u7_113
  have u10_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9084 h hv u2_40 u9_115
  have u11_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31725 h h0 n117 hv u11_118
  have u13_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32457 h h0 hv u12_111
  have u14_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u5_105 u3_109
  have u15_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10626 h hv u2_40 u14_102
  have u16_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u17_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u4_116 hv u16_112
  have u18_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u17_114
  have u19_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u17_114
  have u20_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u21_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u20_88 u5_105 u3_109
  have u22_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u20_88 u5_105 u3_109
  have u23_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u4_116
  have u24_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u25_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u3_109
  have u26_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10067 h hv a41 u8_104
  have u27_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32576 h h0 hv a41 n117 n49 a304
  have u28_42 : T {1, 2, 8} := by
    by_contra hv
    exact c27488 h a304 u27_39 u2_40 hv
  have u29_32 : T {0, 6, 8} := by
    by_contra hv
    exact c27440 h a304 hv u27_39
  have u30_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10344 h hv u27_39 u19_107
  have u31_27 : ¬ T {0, 5, 6} := by
    intro hv
    exact c27437 h a304 hv u28_42
  have u32_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32406 h h0 hv a41 u28_42
  have u33_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c27481 h a304 hv u1_29 u29_32
  have u34_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c27479 h a304 hv u1_29 u29_32
  have u35_55 : T {1, 5, 6} := by
    by_contra hv
    exact c27540 h a304 u31_27 hv u16_112
  have u36_265 : Q {2, 3, 4, 9} := by
    by_contra hv
    exact c1349 h a304 u0_174 u24_230 hv u32_299 u18_302 u13_305
  have u37_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c200 h hv u33_14
  have u38_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c95 h hv u34_7
  have u39_34 : ¬ T {0, 7, 8} := by
    intro hv
    exact c21981 h u36_265 hv u35_55
  have u40_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c295 h hv u38_132 u37_153 u10_173 u26_180 u30_182 u15_184
  have u41_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c506 h hv u39_34
  exact c31443 h u40_177 u22_141 u1_29 u23_200 u21_162 u41_198 u25_196

end BorsukNine.FiniteObstruction

end OAI
