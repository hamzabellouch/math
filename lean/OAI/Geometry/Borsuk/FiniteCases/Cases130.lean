import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases129

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32713 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → ¬ T {4, 7, 8} → T {4, 5, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro a193 n108 a103 n29
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u3_105 hv
  have u5_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv u4_116 a103
  have u6_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31745 h h0 n108 hv u5_114
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c31967 h h0 hv u6_120
  have u8_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c32167 h h0 hv u6_120
  have u9_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31632 h h0 a103 hv
  have u10_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u3_105 u9_118
  have u11_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31641 h h0 n108 hv
  have u12_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31690 h h0 hv u11_113 u10_111
  have u13_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u5_114
  have u14_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31738 h h0 hv u11_113 u13_107
  have u15_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14127 h hv u0_24 u11_113
  have u16_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31646 h h0 hv u10_111
  have u17_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31677 h h0 hv n108 u16_110
  have u18_160 : ¬ Q {0, 2, 5, 6} := by
    intro hv
    exact c7268 h hv u2_49 n108
  have u19_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31663 h h0 hv n108 u3_105
  have u20_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u3_105 u9_118
  have u21_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u20_117
  have u22_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u23_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22074 h hv n29 u22_112 u5_114
  have u24_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13566 h hv n29 u9_118
  have u25_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u4_116
  have u26_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u22_112
  have u27_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1672 h hv u22_112
  have u28_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1670 h hv u22_112
  have u29_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h a193 hv
  have u30_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h a193 hv
  have u31_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13787 h hv u29_26 u13_107 u26_109
  have u32_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c15231 h hv u30_35 u26_109 u6_120
  have u33_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17331 h hv u30_35 u26_109 u6_120
  have u34_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22231 h hv u30_35 u26_109 u6_120
  have u35_208 : Q {1, 2, 3, 7} := by
    by_contra hv
    exact c31535 h h0 u31_206 u15_209 u1_210 u25_207 hv u24_205
  have u36_32 : T {0, 6, 8} := by
    by_contra hv
    exact c13996 h u35_208 hv u21_104
  have u37_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c14107 h u35_208 hv u13_107 u11_113
  have u38_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c13985 h u35_208 hv u4_116
  have u39_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c13987 h u35_208 hv u11_113
  have u40_22 : T {0, 4, 5} := by
    by_contra hv
    exact c13982 h u35_208 hv u14_119
  have u41_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22651 h hv u36_32 u17_106 u20_117
  have u42_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c491 h hv u37_33
  have u43_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23466 h hv u38_23 u12_101 u3_105
  have u44_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c24916 h hv u39_25 u2_49
  have u45_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23039 h hv u40_22 u19_102 a103
  have u46_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c1141 h hv u18_160 u32_216 u34_266 u8_276 u44_286 u27_287
  have u47_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32710 h h0 u23_265 u45_272 u41_269 u43_275 hv
  have u48_253 : Q {1, 5, 6, 9} := by
    by_contra hv
    exact c31376 h h0 u42_197 u11_113 hv u46_288
  have u49_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4328 h hv u47_70 n108
  have u50_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20016 h hv u39_25 u47_70
  exact c826 h u48_253 u49_139 u32_216 u33_231 u7_241 u50_251 u28_252

private theorem c32714 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → T {4, 5, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro n108 a103 n29
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u4_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31632 h h0 a103 hv
  have u5_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u3_105 u4_118
  have u6_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c31797 h h0 hv u5_117
  have u7_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u3_105 hv
  have u8_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv u7_116 a103
  have u9_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c1563 h hv u3_105
  have u10_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u11_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 u10_112
  have u12_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u10_112
  have u13_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c429 h hv n29
  have u14_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c1608 h hv n108
  have u15_120 : T {7, 8, 9} := by
    by_contra hv
    exact c31745 h h0 n108 hv u8_114
  have u16_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c31767 h h0 hv u15_120
  have u17_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c32713 h h0 hv n108 a103 n29
  have u18_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 u17_193 u12_109 hv u1_304
  have u19_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 u17_193 u12_109 hv
  have u20_63 : T {1, 7, 9} := by
    by_contra hv
    exact c939 h u18_249 hv
  have u21_93 : T {3, 5, 8} := by
    by_contra hv
    exact c19850 h u18_249 n29 hv u10_112
  have u22_78 : T {2, 5, 8} := by
    by_contra hv
    exact c19848 h u18_249 n29 hv u10_112
  have u23_67 : T {2, 3, 6} := by
    by_contra hv
    exact c19738 h u18_249 n29 hv
  have u24_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h u19_284 hv
  have u25_46 : T {1, 3, 6} := by
    by_contra hv
    exact c24638 h u19_284 n29 hv
  have u26_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24748 h u19_284 n29 hv u10_112
  have u27_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8789 h hv u20_63 u24_84 u15_120
  have u28_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4005 h hv u22_78 u21_93 u7_116
  have u29_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9045 h hv u26_57 u22_78 u7_116
  have u30_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c3623 h hv u23_67 u15_120
  have u31_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6563 h hv u25_46 u15_120
  have u32_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c327 h hv u30_134 u31_155 u27_170 u16_185 u13_187 u6_188
  exact c347 h u2_24 u28_136 u11_157 u29_172 u32_186 u9_189 u14_192 u17_193

private theorem c32715 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 7, 9} → T {4, 5, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro n193 a103 n29
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u2_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u3_108 : T {4, 7, 8} := by
    by_contra hv
    exact c32714 h h0 hv a103 n29
  have u4_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31672 h h0 u3_108 hv a103
  have u5_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c1578 h hv u4_106
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u6_112
  have u8_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31668 h h0 hv u3_108 u7_109
  have u9_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c1518 h hv u8_102
  have u10_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u11_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31632 h h0 a103 hv
  have u12_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u10_105 u11_118
  have u13_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u12_117
  have u14_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u3_108 hv
  have u15_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31711 h h0 u14_113 hv u13_104
  have u16_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u10_105 u11_118
  have u17_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c31857 h h0 hv u16_111
  have u18_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u10_105 hv
  have u19_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c1563 h hv u10_105
  have u20_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 u6_112
  have u21_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c429 h hv n29
  have u22_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31322 h h0 n193 u7_109 hv u1_304
  have u23_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 n193 u7_109 hv
  have u24_63 : T {1, 7, 9} := by
    by_contra hv
    exact c939 h u22_249 hv
  have u25_93 : T {3, 5, 8} := by
    by_contra hv
    exact c19850 h u22_249 n29 hv u6_112
  have u26_78 : T {2, 5, 8} := by
    by_contra hv
    exact c19848 h u22_249 n29 hv u6_112
  have u27_67 : T {2, 3, 6} := by
    by_contra hv
    exact c19738 h u22_249 n29 hv
  have u28_84 : T {2, 7, 9} := by
    by_contra hv
    exact c1254 h u23_284 hv
  have u29_46 : T {1, 3, 6} := by
    by_contra hv
    exact c24638 h u23_284 n29 hv
  have u30_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24748 h u23_284 n29 hv u6_112
  have u31_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9215 h hv u24_63 u28_84 u15_115
  have u32_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4005 h hv u26_78 u25_93 u18_116
  have u33_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9045 h hv u30_57 u26_78 u18_116
  have u34_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4045 h hv u27_67 u15_115
  have u35_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c6985 h hv u29_46 u15_115
  have u36_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c374 h hv u34_137 u35_158 u31_173 u21_187 u5_190 u17_194
  exact c347 h u2_24 u32_136 u20_157 u33_172 u9_186 u19_189 u36_192 n193

theorem c32716 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro a103 n29
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32712 h h0 hv n29
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u3_105 hv
  have u5_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13845 h hv u0_24 u4_116
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u6_112
  have u8_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1672 h hv u6_112
  have u9_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c1670 h hv u6_112
  have u10_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31632 h h0 a103 hv
  have u11_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv u4_116 a103
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u3_105 u10_118
  have u13_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u3_105 u10_118
  have u14_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13566 h hv n29 u10_118
  have u15_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u11_114
  have u16_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22074 h hv n29 u6_112 u11_114
  have u17_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c31646 h h0 hv u12_111
  have u18_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c31634 h h0 hv u13_117
  have u19_108 : T {4, 7, 8} := by
    by_contra hv
    exact c32714 h h0 hv a103 n29
  have u20_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u19_108 hv
  have u21_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31668 h h0 hv u19_108 u7_109
  have u22_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13775 h hv u0_24 u19_108 u7_109
  have u23_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c31672 h h0 u19_108 hv a103
  have u24_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31691 h h0 u20_113 hv u6_112
  have u25_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31741 h h0 hv u20_113 u10_118
  have u26_115 : T {5, 7, 9} := by
    by_contra hv
    exact c31711 h h0 u20_113 hv u18_104
  have u27_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7968 h hv u2_49 u21_102
  have u28_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c1580 h hv u23_106
  have u29_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c1582 h hv u23_106
  have u30_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32715 h h0 hv a103 n29
  have u31_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h u30_193 hv
  have u32_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h u30_193 hv
  have u33_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14211 h hv u31_26 u15_107 u7_109
  have u34_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c15939 h hv u32_35 u7_109 u26_115
  have u35_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18039 h hv u32_35 u7_109 u26_115
  have u36_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22939 h hv u32_35 u7_109 u26_115
  have u37_208 : Q {1, 2, 3, 7} := by
    by_contra hv
    exact c31535 h h0 u22_206 u33_209 u1_210 u5_207 hv u14_205
  have u38_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c14109 h u37_208 hv u15_107 u25_119
  have u39_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c13985 h u37_208 hv u4_116
  have u40_25 : T {0, 4, 8} := by
    by_contra hv
    exact c14062 h u37_208 hv u23_106 u17_110
  have u41_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c13983 h u37_208 hv u25_119
  have u42_27 : T {0, 5, 6} := by
    by_contra hv
    exact c14078 h u37_208 hv u6_112 u20_113
  have u43_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c495 h hv u38_33
  have u44_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22618 h hv u39_23 u3_105 u23_106
  have u45_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c23055 h hv u40_25 a103 u19_108
  have u46_292 : ¬ Q {2, 6, 7, 8} := by
    intro hv
    exact c25756 h hv u41_22 u2_49
  have u47_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23483 h hv u42_27 u24_101 u12_111
  have u48_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c1216 h hv u27_165 u34_221 u36_271 u29_281 u8_287 u46_292
  have u49_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32710 h h0 u16_265 u45_272 u44_269 u47_275 hv
  have u50_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u43_203 u48_294 hv u25_119
  have u51_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5028 h hv u49_70 u21_102
  have u52_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c20856 h hv u41_22 u49_70
  have u53_259 : Q {1, 6, 8, 9} := by
    by_contra hv
    exact c31621 h h0 u50_314 hv u43_203 u48_294
  exact c901 h u53_259 u51_144 u34_221 u35_236 u28_246 u9_252 u52_257

end BorsukNine.FiniteObstruction

end OAI
