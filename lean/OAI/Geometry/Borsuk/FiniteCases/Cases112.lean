import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases111

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32578 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {3, 6, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a95 n49 a304
  have u0_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u2_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u1_116 hv u0_112
  have u3_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u2_114
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u1_116
  have u7_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u5_88 u6_105 u4_109
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u5_88 u6_105 u4_109
  have u9_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u1_116
  have u10_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u11_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u10_29 hv
  have u12_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15959 h hv u10_29 u5_88
  have u13_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c725 h hv n49
  have u14_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u15_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u14_118
  have u16_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u4_109
  have u17_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2657 h hv a95 u15_103
  have u18_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14975 h hv u10_29 a95
  have u19_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c32574 h h0 hv a95 n49 a304
  have u20_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31725 h h0 u19_117 hv u14_118
  have u21_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16501 h hv a95 u6_105 u20_111
  have u22_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32577 h h0 hv u19_117 n49 a304
  have u23_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c615 h hv u22_41
  have u24_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9646 h hv u22_41 u3_107
  have u25_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c640 h hv u17_127 u13_210 u18_215 u12_222 u23_224 u21_225
  have u26_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c31390 h u12_222 hv u21_225 u23_224 u18_215 u13_210 u25_219
  have u27_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u24_177 u8_141 u10_29 u9_200 u7_162 hv u16_196
  have u28_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11068 h hv u11_40 u22_41 u26_43
  exact c434 h u27_198 u8_141 u7_162 u24_177 u28_187 u16_196 u9_200

private theorem c32579 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n117 n49 a304
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u1_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32578 h h0 hv n49 a304
  have u2_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1950 h hv u1_95 u0_116
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u4_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u0_116
  have u5_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u4_105 u3_109
  have u6_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7968 h hv n49 u5_102
  have u7_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u4_105 u3_109
  have u8_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u7_108 hv
  have u9_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv u7_108
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u11_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u0_116 hv u10_112
  have u12_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u11_114
  have u13_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u14_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u13_88 u4_105 u3_109
  have u15_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u13_88 u4_105 u3_109
  have u16_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u13_88 u4_105 u3_109
  have u17_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u13_88 u4_105 u3_109
  have u18_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u0_116
  have u19_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u20_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u19_29 hv
  have u21_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u22_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u23_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u22_118
  have u24_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u21_99 u23_103
  have u25_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u3_109
  have u26_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u27_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c1743 h hv n117
  have u28_104 : T {4, 5, 9} := by
    by_contra hv
    exact c31633 h h0 hv n117
  have u29_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31725 h h0 n117 hv u22_118
  have u30_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c32577 h h0 hv n117 n49 a304
  have u31_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c31712 h h0 hv u28_104 u8_113
  have u32_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5137 h hv u26_90 u28_104 u3_109
  have u33_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c31857 h h0 hv u29_111
  have u34_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv u30_41
  have u35_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9646 h hv u30_41 u12_107
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9084 h hv u20_40 u31_115
  have u37_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c31532 h h0 u2_122 u34_125 u24_124 hv u17_123 u16_126
  have u38_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u35_177 u15_141 u19_29 u18_200 u14_162 hv u25_196
  have u39_43 : T {1, 2, 9} := by
    by_contra hv
    exact c633 h u37_127 hv
  have u40_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c2747 h u37_127 hv u29_111 u11_114
  have u41_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c2645 h u37_127 hv u11_114
  have u42_91 : T {3, 5, 6} := by
    by_contra hv
    exact c2678 h u37_127 u41_87 hv u1_95
  have u43_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c434 h u38_198 u15_141 u14_162 u35_177 hv u25_196 u18_200
  have u44_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c31899 h h0 u38_198 hv u39_43
  have u45_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13284 h hv u44_38 u40_92
  have u46_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4141 h hv u42_91 u29_111 u8_113
  have u47_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7081 h hv u42_91 u29_111 u8_113
  have u48_190 : Q {0, 4, 6, 8} := by
    by_contra hv
    exact c370 h u43_187 u46_137 u47_158 u36_173 hv u9_192 u33_194
  have u49_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10062 h hv u44_38 u31_115
  exact c475 h u48_190 u32_144 u6_165 u49_180 u25_196 u27_201 u45_203

private theorem c32580 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n41 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u2_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u2_116
  have u4_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u5_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u2_116 hv u4_112
  have u6_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u7_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u2_116
  have u8_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u6_88 u7_105 u0_109
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u6_88 u7_105 u0_109
  have u10_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u1_29 hv
  have u11_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u7_105 u0_109
  have u12_178 : ¬ Q {0, 3, 5, 9} := by
    intro hv
    exact c9784 h hv u10_40 u11_108
  have u13_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u5_114
  have u14_117 : T {6, 7, 8} := by
    by_contra hv
    exact c32579 h h0 hv n49 a304
  have u15_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u14_117
  have u16_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u15_104 hv u13_107
  have u17_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31750 h h0 u14_117 hv u5_114
  have u18_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8662 h hv u10_40 u17_120
  have u19_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c32572 h h0 hv u18_170 u16_110 u12_178 u9_162 u8_141 u5_114 u3_200 u1_29 u0_109
  have u20_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u14_117
  have u21_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32578 h h0 hv n49 a304
  have u22_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1950 h hv u21_95 u2_116
  have u23_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u5_114
  have u24_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u6_88 u7_105 u0_109
  have u25_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u6_88 u7_105 u0_109
  have u26_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u27_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u28_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u29_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u28_118
  have u30_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u27_99 u29_103
  have u31_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c603 h hv n41
  have u32_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9226 h hv n41 u4_112
  have u33_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c31532 h h0 u22_122 u31_125 u30_124 hv u25_123 u24_126
  have u34_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1349 h a304 u32_174 u26_230 u19_265 u20_299 u23_302 hv
  have u35_86 : ¬ T {3, 4, 5} := by
    intro hv
    exact c2643 h u33_127 hv u14_117
  have u36_39 : T {1, 2, 5} := by
    by_contra hv
    exact c27628 h u34_305 hv u10_40 n41
  have u37_298 : ¬ Q {3, 4, 5, 8} := by
    intro hv
    exact c1288 h hv u35_86
  have u38_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c27581 h u34_305 hv u36_39
  exact c31528 h h0 u38_31 u37_298 u21_95 n49 u28_118

private theorem c32581 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → T {1, 2, 7} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → T {4, 6, 7} → ¬ Q {0, 5, 8, 9} → T {0, 5, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro a43 a41 n162 n141 a105 n200 a29 n196
  have u0_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31790 h h0 hv a41 a43
  have u1_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9649 h hv a43 a105
  have u2_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c434 h hv n141 n162 u1_177 u0_187 n196 n200
  exact c31443 h u1_177 n141 a29 n200 n162 u2_198 n196

theorem c32582 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n49 a304
  have u0_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u1_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u2_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u1_118
  have u3_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u0_99 u2_103
  have u4_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u4_109
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u7_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u8_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u9_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u8_29 hv
  have u10_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32571 h h0 hv n49 a304
  have u11_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u10_116
  have u12_105 : T {4, 6, 7} := by
    by_contra hv
    exact c31635 h h0 hv u10_116
  have u13_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u10_116 hv u6_112
  have u14_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u7_88 u12_105 u4_109
  have u15_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u7_88 u12_105 u4_109
  have u16_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4709 h hv u7_88 u12_105 u4_109
  have u17_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv u12_105 u4_109
  have u18_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u12_105 u4_109
  have u19_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7649 h hv u7_88 u12_105 u4_109
  have u20_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31640 h h0 hv u13_114
  have u21_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv u17_108
  have u22_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u17_108 hv
  have u23_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31629 h h0 u18_102 hv
  have u24_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c32578 h h0 hv n49 a304
  have u25_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1950 h hv u24_95 u10_116
  have u26_117 : T {6, 7, 8} := by
    by_contra hv
    exact c32579 h h0 hv n49 a304
  have u27_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u26_117
  have u28_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31720 h h0 u26_117 hv u12_105
  have u29_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31732 h h0 hv u23_119 u26_117
  have u30_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u27_104 hv u20_107
  have u31_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31715 h h0 u27_104 hv u10_116
  have u32_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c6988 h hv n49 u28_111
  have u33_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4164 h hv u24_95 u28_111 u1_118
  have u34_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c1578 h hv u29_106
  have u35_41 : T {1, 2, 7} := by
    by_contra hv
    exact c32580 h h0 hv n49 a304
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9087 h hv u35_41 u22_113
  have u37_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32581 h h0 hv u35_41 u19_162 u16_141 u12_105 u11_200 u8_29 u5_196
  have u38_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c633 h hv u37_43
  have u39_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11048 h hv u37_43 u24_95
  have u40_125 : Q {0, 1, 2, 7} := by
    by_contra hv
    exact c31532 h h0 u25_122 hv u3_124 u38_127 u14_123 u15_126
  have u41_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c376 h hv u33_137 u32_158 u36_173 u39_187 u34_190 u21_192
  have u42_89 : ¬ T {3, 4, 8} := by
    intro hv
    exact c2441 h u40_125 hv u2_103 u30_110
  have u43_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c31431 h u36_173 u33_137 u39_187 u41_194 u21_192 hv u32_158
  have u44_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12726 h hv u9_40 u42_89
  have u45_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c28278 h hv u43_25 u9_40
  have u46_290 : ¬ Q {2, 5, 7, 9} := by
    intro hv
    exact c25590 h hv u43_25 u42_89 u29_106
  exact c31335 h h0 u31_115 u45_310 u46_290 u44_199

end BorsukNine.FiniteObstruction

end OAI
