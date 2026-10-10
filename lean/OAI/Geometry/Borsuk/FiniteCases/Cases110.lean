import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases109

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32570 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {3, 6, 7} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n95 a116 n49 a304
  have u0_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c31529 h h0 hv a116 n49 a304
  have u1_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u2_31 : ¬ T {0, 6, 7} := by
    intro hv
    exact c32569 h h0 hv n95 a116 n49 a304
  have u3_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25738 h hv u2_31 n95 u1_105
  have u4_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20838 h hv u2_31 n95 u1_105
  have u5_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 a116 hv u0_311 u3_291
  exact c31604 h h0 u5_200 u3_291 u4_256 u0_311

theorem c32571 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a116 n49 a304
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u1_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u0_29 hv
  have u2_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32447 h h0 a304 hv
  have u3_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv n49 u2_112
  have u4_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u5_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u6_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u7_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u6_118
  have u8_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u5_99 u7_103
  have u9_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u9_109
  have u11_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u12_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1320 h a304 hv
  have u13_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u14_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv a116 u7_103
  have u15_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u13_105 u6_118
  have u16_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u13_105 u6_118
  have u17_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv n49 u13_105
  have u18_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u14_114
  have u19_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u14_114
  have u20_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u1_40 u14_114
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32457 h h0 hv u15_111
  have u22_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2509 h hv u11_90 u15_111
  have u23_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u16_117
  have u24_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2089 h hv u11_90 u16_117
  have u25_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u11_90 u19_107 u9_109
  have u26_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c31531 h h0 hv a116 n49 a304
  have u27_95 : T {3, 6, 7} := by
    by_contra hv
    exact c32570 h h0 hv a116 n49 a304
  have u28_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1951 h hv u27_95 a116
  have u29_125 : Q {0, 1, 2, 7} := by
    by_contra hv
    exact c31532 h h0 u28_122 hv u8_124 u26_127 u24_123 u22_126
  have u30_41 : T {1, 2, 7} := by
    by_contra hv
    exact c603 h u29_125 hv
  have u31_87 : ¬ T {3, 4, 6} := by
    intro hv
    exact c2365 h u29_125 hv a116
  have u32_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9647 h hv u30_41 u19_107
  have u33_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27159 h hv u0_29 u30_41
  have u34_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31443 h u32_177 u25_141 u0_29 hv u17_162 u18_198 u10_196
  have u35_265 : Q {2, 3, 4, 9} := by
    by_contra hv
    exact c1349 h a304 u20_174 u4_230 hv u23_299 u33_302 u21_305
  have u36_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c436 h u34_200 u25_141 u17_162 u32_177 hv u10_196 u18_198
  have u37_47 : ¬ T {1, 3, 7} := by
    intro hv
    exact c12975 h u34_200 hv u12_88 u27_95
  have u38_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c12977 h u34_200 hv u12_88 u27_95
  have u39_51 : T {1, 4, 6} := by
    by_contra hv
    exact c12982 h u34_200 hv u31_87 u13_105
  have u40_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1042 h u35_265 hv
  have u41_57 : T {1, 5, 8} := by
    by_contra hv
    exact c22076 h u35_265 hv u2_112 u14_114
  have u42_82 : T {2, 6, 9} := by
    by_contra hv
    exact c11052 h u36_187 u37_47 hv
  have u43_61 : T {1, 6, 9} := by
    by_contra hv
    exact c11058 h u36_187 hv u38_68
  have u44_84 : ¬ T {2, 7, 9} := by
    intro hv
    exact c11133 h u36_187 u40_70 u42_82 hv
  have u45_46 : T {1, 3, 6} := by
    by_contra hv
    exact c11076 h u36_187 hv u37_47 n49
  have u46_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c1008 h hv u38_68
  have u47_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7837 h hv u41_57 u11_90
  have u48_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8289 h hv u45_46 u39_51 u43_61
  have u49_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7441 h hv u45_46 u39_51 u43_61
  have u50_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c1248 h hv u44_84
  exact c184 h u29_125 u46_152 u3_157 u49_161 u47_164 u48_167 u50_168

theorem c32572 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 3, 4, 9} → ¬ Q {0, 3, 4, 5} → T {4, 8, 9} → ¬ Q {0, 3, 5, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 1, 5, 8} → T {5, 7, 8} → ¬ Q {0, 5, 8, 9} → T {0, 5, 8} → T {4, 7, 9} → False := by
  classical
  intro a265 n170 a110 n178 n162 n141 a114 n200 a29 a109
  have u0_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv a109
  have u1_65 : T {2, 3, 4} := by
    by_contra hv
    exact c975 h a265 hv
  have u2_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1042 h a265 hv
  have u3_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1117 h a265 hv
  have u4_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c21965 h a265 hv a114
  have u5_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c21975 h a265 a29 hv
  have u6_60 : T {1, 6, 8} := by
    by_contra hv
    exact c22034 h a265 u4_5 u5_59 hv
  have u7_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31905 h h0 hv u1_65 u2_70
  have u8_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c3011 h hv u3_75 a109 a110
  have u9_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9477 h hv u3_75 a109 a110
  have u10_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9517 h hv u6_60 u3_75
  have u11_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5873 h hv u6_60 a109
  have u12_177 : Q {0, 3, 5, 8} := by
    by_contra hv
    exact c31443 h hv n141 a29 n200 n162 u7_198 u0_196
  exact c254 h u12_177 u8_129 u11_150 n170 u9_175 u10_176 n178

theorem c32573 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 3, 4, 9} → T {6, 7, 8} → T {3, 6, 7} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro n174 a117 a95 n49 a304
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
  have u14_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv a117
  have u15_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31681 h h0 u14_104 hv u13_107
  have u16_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31750 h h0 a117 hv u5_114
  have u17_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8662 h hv u10_40 u16_120
  have u18_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c32572 h h0 hv u17_170 u15_110 u12_178 u9_162 u8_141 u5_114 u3_200 u1_29 u0_109
  have u19_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u16_120
  have u20_204 : ¬ Q {0, 7, 8, 9} := by
    intro hv
    exact c1788 h hv u16_120
  have u21_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv u7_105 u0_109
  have u22_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31649 h h0 hv u21_102 u14_104
  have u23_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7805 h hv a95 u7_105 a117
  have u24_142 : ¬ Q {0, 1, 5, 9} := by
    intro hv
    exact c4865 h hv a95 u7_105 a117
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31629 h h0 u21_102 hv
  have u26_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31732 h h0 hv u25_119 a117
  have u27_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31720 h h0 a117 hv u7_105
  have u28_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv a117
  have u29_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u30_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u29_118
  have u31_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2657 h hv a95 u30_103
  have u32_184 : ¬ Q {0, 3, 8, 9} := by
    intro hv
    exact c10626 h hv u10_40 u21_102
  have u33_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 u11_108 hv
  have u34_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c32427 h h0 hv u5_114
  have u35_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2583 h hv u6_88 u7_105 u0_109
  have u36_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2153 h hv u6_88 u7_105 u0_109
  have u37_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c1734 h hv u2_116
  have u38_240 : ¬ Q {1, 3, 8, 9} := by
    intro hv
    exact c735 h hv n49
  have u39_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u40_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c723 h hv n49
  have u41_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u42_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u41_99 u30_103
  have u43_305 : Q {3, 4, 8, 9} := by
    by_contra hv
    exact c1349 h a304 n174 u39_230 u18_265 u28_299 u34_302 hv
  have u44_89 : T {3, 4, 8} := by
    by_contra hv
    exact c1335 h u43_305 hv
  have u45_28 : T {0, 5, 7} := by
    by_contra hv
    exact c27578 h u43_305 hv u10_40
  have u46_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2367 h hv u44_89 u33_113
  have u47_122 : Q {0, 1, 2, 4} := by
    by_contra hv
    exact c31532 h h0 hv u46_125 u42_124 u31_127 u36_123 u35_126
  have u48_38 : T {1, 2, 4} := by
    by_contra hv
    exact c558 h u47_122 hv
  have u49_93 : T {3, 5, 8} := by
    by_contra hv
    exact c2020 h u47_122 hv u4_112 u2_116
  have u50_91 : T {3, 5, 6} := by
    by_contra hv
    exact c2002 h u47_122 hv u27_111 u4_112
  have u51_96 : ¬ T {3, 6, 8} := by
    intro hv
    exact c1971 h u47_122 u50_91 a95 hv
  have u52_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c1981 h u47_122 hv a95 u41_99
  have u53_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10203 h hv u48_38 u5_114
  have u54_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28841 h hv u45_28 u48_38
  have u55_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8233 h hv u49_93 u30_103 u5_114
  have u56_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5293 h hv u49_93 u30_103 u5_114
  have u57_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c31310 h h0 hv u51_96
  have u58_147 : ¬ Q {0, 1, 7, 9} := by
    intro hv
    exact c5580 h hv u51_96 u26_106 u4_112
  have u59_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8520 h hv u51_96 u26_106 u4_112
  have u60_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12026 h hv u10_40 u52_92
  have u61_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8652 h hv u52_92 u21_102 u27_111
  have u62_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5712 h hv u52_92 u21_102 u27_111
  have u63_275 : Q {2, 3, 8, 9} := by
    by_contra hv
    exact c1495 h u43_305 u32_184 u38_240 hv u37_311 u54_314 u19_315
  have u64_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c216 h hv u31_127 u57_159 u23_163 u55_166 u59_168 u61_169
  have u65_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c539 h hv u62_148 u61_169 u32_184 u60_194 u3_200 u20_204
  have u66_138 : ¬ Q {0, 1, 4, 9} := by
    intro hv
    exact c113 h hv u31_127 u40_133 u24_142 u56_145 u58_147 u62_148
  have u67_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c527 h hv u62_148 u61_169 u32_184 u60_194 u3_200 u65_203 u20_204
  have u68_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c107 h hv u31_127 u40_133 u66_138 u24_142 u56_145 u58_147 u62_148
  have u69_276 : Q {2, 4, 5, 6} := by
    by_contra hv
    exact c31262 h h0 u63_275 hv u22_101
  have u70_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c314 h hv u40_133 u64_154 n174 u12_178 u53_181 u32_184
  have u71_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c31485 h u12_178 hv u70_183 u32_184 u40_133 u64_154 n174
  exact c23556 h u69_276 u68_8 u71_21 u67_36

end BorsukNine.FiniteObstruction

end OAI
