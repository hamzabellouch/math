import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases131

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32721 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 9} → ¬ Q {3, 5, 7, 9} → T {0, 8, 9} → T {4, 7, 8} → ¬ T {6, 7, 8} → Q {3, 6, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro a109 n310 a36 a108 n117 a313 n105
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u4_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u5_104 : T {4, 5, 9} := by
    by_contra hv
    exact c31633 h h0 hv n117
  have u6_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h a313 hv
  have u7_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13567 h hv u0_29 u6_118
  have u8_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h a313 u0_29 hv
  have u9_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 a313 hv
  have u10_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u11_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u1_24 u10_116
  have u12_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 a109 hv
  have u13_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31756 h h0 hv u6_118 a109
  have u14_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13775 h hv u1_24 a108 a109
  have u15_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31680 h h0 u5_104 hv a109
  have u16_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10482 h hv u8_38 u12_112
  have u17_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31733 h h0 n117 hv u12_112
  have u18_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u13_120
  have u19_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14119 h hv a36 u10_116 u17_119
  have u20_274 : Q {2, 3, 7, 9} := by
    by_contra hv
    exact c1484 h a313 u16_183 u3_239 hv u2_304 n310 u18_315
  have u21_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c31535 h h0 u14_206 hv u4_210 u11_207 u19_208 u7_205
  have u22_57 : T {1, 5, 8} := by
    by_contra hv
    exact c23352 h u20_274 hv u9_103 u12_112
  have u23_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c23233 h u20_274 hv u22_57
  exact c14194 h u21_209 u23_23 n105 u15_107

theorem c32722 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 6, 7, 8} → ¬ Q {1, 3, 6, 7} → ¬ Q {0, 3, 6, 7} → ¬ Q {2, 3, 6, 7} → T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  classical
  intro n312 n235 n179 n270 a95 n105
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
  have u9_306 : Q {3, 5, 6, 7} := by
    by_contra hv
    exact c32718 h n235 n312 n270 a95 hv u8_300 n179
  have u10_91 : T {3, 5, 6} := by
    by_contra hv
    exact c1361 h u9_306 hv
  have u11_92 : T {3, 5, 7} := by
    by_contra hv
    exact c1376 h u9_306 hv
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h u9_306 hv
  have u13_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 u9_306 hv
  have u14_313 : Q {3, 6, 7, 9} := by
    by_contra hv
    exact c1422 h u9_306 n179 n235 n270 u8_300 n312 hv
  have u15_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16375 h hv u1_24 u10_91
  have u16_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1453 h u14_313 hv
  have u17_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1764 h u14_313 hv
  have u18_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c32537 h h0 u14_313 hv
  have u19_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28701 h u14_313 u4_29 hv
  have u20_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c31787 h h0 hv u17_118
  have u21_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31726 h h0 u12_111 hv u17_118
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31673 h h0 u13_110 hv u18_103
  have u23_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31675 h h0 hv u13_110 u18_103
  have u24_36 : T {0, 8, 9} := by
    by_contra hv
    exact c27720 h u9_306 hv u19_38
  have u25_310 : ¬ Q {3, 5, 7, 9} := by
    intro hv
    exact c32507 h h0 hv u22_106
  have u26_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2653 h hv u11_92 u22_106
  have u27_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv u23_108
  have u28_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c32721 h h0 hv u25_310 u24_36 u23_108 u21_117 u14_313 n105
  have u29_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u28_109 hv
  have u30_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u28_109 n105
  have u31_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31685 h h0 u13_110 u28_109 hv
  have u32_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u29_112 hv u7_116
  have u33_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c32547 h h0 hv u30_102
  have u34_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16047 h hv u1_24 u30_102 u23_108
  have u35_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23047 h hv u1_24 u30_102 u23_108
  have u36_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c31897 h h0 hv u31_107
  have u37_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4733 h hv u16_97 u31_107 u17_118
  have u38_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10202 h hv u19_38 u32_114
  have u39_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1454 h u14_313 u38_181 u2_237 u35_272 hv u27_308 u33_314
  have u40_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1305 h u39_302 hv
  have u41_41 : ¬ T {1, 2, 7} := by
    intro hv
    exact c27159 h u39_302 u4_29 hv
  have u42_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16239 h hv u4_29 u40_87
  have u43_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c640 h hv u26_127 u3_210 u5_215 u34_222 u42_224 u15_225
  have u44_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c32708 h h0 u42_224 u34_222 u15_225 u43_219 u26_127 hv
  have u45_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9648 h hv u44_43 n105
  have u46_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12328 h hv u19_38 u41_41 u44_43
  exact c32648 h u37_141 u20_187 u46_196 u36_198 u4_29 u45_177 u6_162

private theorem c32723 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 4} → ¬ Q {0, 3, 4, 6} → ¬ Q {2, 3, 4, 6} → ¬ Q {3, 4, 6, 8} → T {5, 7, 9} → ¬ Q {1, 2, 3, 5} → ¬ Q {2, 3, 5, 6} → ¬ Q {1, 3, 5, 6} → ¬ T {7, 8, 9} → ¬ Q {3, 5, 6, 9} → Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → ¬ T {4, 6, 7} → False := by
  classical
  intro n38 n171 n262 n301 a115 n206 n266 n231 n120 n308 a306 a312 n105
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u4_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u5_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u3_104 u4_110 hv
  have u6_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c13993 h hv u1_29 u5_107
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u4_110 u3_104 hv
  have u8_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c32477 h h0 hv u7_109
  have u9_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u10_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u9_116
  have u11_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u12_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c560 h hv n38
  have u13_30 : T {0, 5, 9} := by
    by_contra hv
    exact c28560 h a312 hv n38
  have u14_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9362 h hv n38 n120
  have u15_209 : Q {1, 2, 3, 8} := by
    by_contra hv
    exact c31535 h h0 n206 hv u2_210 u10_207 u6_208 u12_205
  have u16_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16755 h hv u13_30 a115 u9_116
  have u17_296 : Q {3, 4, 5, 6} := by
    by_contra hv
    exact c1362 h a306 u14_175 n231 n266 hv u8_307 n308
  have u18_42 : T {1, 2, 8} := by
    by_contra hv
    exact c620 h u15_209 hv
  have u19_26 : ¬ T {0, 4, 9} := by
    intro hv
    exact c14211 h u15_209 hv u5_107 u7_109
  have u20_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1300 h u17_296 n171 u16_227 n262 u11_300 n301 hv
  have u21_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32435 h h0 hv u18_42 u20_302
  exact c28558 h a312 u19_26 u21_39

theorem c32724 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → ¬ Q {0, 2, 4, 9} → Q {3, 5, 6, 7} → Q {3, 6, 7, 8} → ¬ Q {0, 3, 6, 7} → ¬ Q {0, 1, 2, 4} → ¬ T {4, 6, 7} → False := by
  classical
  intro a108 n159 a306 a312 n179 n122 n105
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u3_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c32527 h h0 a312 hv
  have u4_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c32467 h h0 a306 hv
  have u5_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31681 h h0 u3_104 u4_110 hv
  have u6_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31640 h h0 u5_107 hv
  have u7_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6708 h hv u0_49 u6_114
  have u8_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31683 h h0 u4_110 u3_104 hv
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31644 h h0 u8_109 hv
  have u10_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 u9_112
  have u11_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32497 h h0 hv u5_107
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1749 h a312 hv
  have u13_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1659 h a306 hv
  have u14_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31726 h h0 u13_111 u12_117 hv
  have u15_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u14_118
  have u16_92 : T {3, 5, 7} := by
    by_contra hv
    exact c1376 h a306 hv
  have u17_96 : T {3, 6, 8} := by
    by_contra hv
    exact c1438 h a312 hv
  have u18_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u19_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c1569 h hv n105
  have u20_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 a108 hv
  have u21_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c32487 h h0 hv a108
  have u22_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31672 h h0 a108 hv u15_103
  have u23_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31748 h h0 a108 hv u12_117
  have u24_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31668 h h0 hv a108 u8_109
  have u25_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17299 h hv u1_24 a108 u8_109
  have u26_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22199 h hv u1_24 a108 u8_109
  have u27_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13775 h hv u1_24 a108 u8_109
  have u28_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31741 h h0 hv u20_113 u14_118
  have u29_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31711 h h0 u20_113 hv u3_104
  have u30_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31691 h h0 u20_113 hv u9_112
  have u31_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1584 h hv u22_106
  have u32_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c1794 h hv u23_120
  have u33_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c1524 h hv u24_102
  have u34_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6669 h hv u17_96 u12_117 u28_119
  have u35_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7089 h hv u16_92 u13_111 u29_115
  have u36_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u10_157 u35_158 n159 hv u7_156 n122 u34_155
  have u37_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18182 h hv u36_10 u20_113
  have u38_64 : T {1, 8, 9} := by
    by_contra hv
    exact c27710 h a306 u36_10 hv
  have u39_58 : T {1, 5, 9} := by
    by_contra hv
    exact c28550 h a312 u36_10 hv
  have u40_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9079 h hv u38_64 u18_116 u28_119
  have u41_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21821 h hv u38_64 u18_116 u28_119
  have u42_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6161 h hv u38_64 u30_101
  have u43_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21657 h hv u39_58 u29_115 u18_116
  have u44_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8915 h hv u39_58 u29_115 u18_116
  have u45_38 : T {1, 2, 4} := by
    by_contra hv
    exact c32723 h h0 hv u44_171 u43_262 u31_301 u29_115 u27_206 u26_266 u25_231 u23_120 u21_308 a306 a312 n105
  have u46_36 : ¬ T {0, 8, 9} := by
    intro hv
    exact c27721 h a306 hv u45_38
  have u47_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32534 h h0 a312 hv u45_38
  have u48_30 : ¬ T {0, 5, 9} := by
    intro hv
    exact c28561 h a312 hv u45_38
  have u49_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9503 h hv u45_38 u28_119
  have u50_85 : T {2, 8, 9} := by
    by_contra hv
    exact c27838 h a306 u46_36 hv u4_110
  have u51_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10484 h hv u47_39 u22_106
  have u52_273 : ¬ Q {2, 3, 7, 8} := by
    intro hv
    exact c23210 h hv u48_30 u3_104 u20_113
  have u53_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16921 h hv u50_85 u18_116 u28_119
  have u54_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3221 h hv u50_85 u30_101
  have u55_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c284 h hv u54_131 u42_152 u40_172 u49_176 n179 u51_183
  have u56_303 : Q {3, 4, 7, 8} := by
    by_contra hv
    exact c1469 h a312 u55_182 u37_238 u52_273 hv u11_309 u32_315
  exact c1319 h u56_303 u40_172 u53_228 u41_263 u33_297 u19_300 u2_304

end BorsukNine.FiniteObstruction

end OAI
