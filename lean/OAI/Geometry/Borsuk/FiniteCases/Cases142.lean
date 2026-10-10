import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases141

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32800 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → False := by
  classical
  intro a309
  have u0_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  exact c1393 h a309 u0_93

theorem c32801 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 3, 4, 7} → ¬ Q {0, 4, 7, 9} → ¬ Q {0, 1, 4, 7} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 5, 7} → ¬ Q {0, 2, 4, 7} → False := by
  classical
  intro n172 n193 n136 n192 n186 n157
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c357 h hv n136 n157 n172 n186 n192 n193
  exact c347 h u0_24 n136 n157 n172 n186 u1_189 n192 n193

private theorem c32802 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → ¬ T {2, 6, 9} → ¬ T {6, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro a198 n82 n118 n107
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u2_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u3_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  have u4_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u5_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv n118
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31704 h h0 hv u5_103 u4_114
  have u7_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4008 h hv u3_93 u6_112 u0_116
  have u8_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u2_49 u6_112
  have u9_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31735 h h0 hv n107 n118
  have u10_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c31837 h h0 hv u9_113
  have u11_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31739 h h0 hv n107 n118
  have u12_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c31777 h h0 hv u11_119
  have u13_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c12597 h a198 u1_51 hv
  have u14_90 : T {3, 4, 9} := by
    by_contra hv
    exact c12690 h a198 u2_49 u13_70 hv
  have u15_61 : T {1, 6, 9} := by
    by_contra hv
    exact c12716 h a198 hv n82 n107
  have u16_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c12587 h a198 hv u14_90
  have u17_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9071 h hv u15_61 u9_113 u11_119
  have u18_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c11886 h hv u16_40 u3_93
  exact c32801 h h0 u17_172 u18_193 u7_136 u10_192 u12_186 u8_157

private theorem c32803 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {2, 6, 9} → ¬ T {6, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n82 n118 n107
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u2_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c32786 h h0 hv
  have u3_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c32800 h h0 hv
  have u4_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u5_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u6_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u7_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u8_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv n118
  have u9_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31704 h h0 hv u8_103 u7_114
  have u10_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u9_112
  have u11_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c1668 h hv u9_112
  have u12_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4730 h hv n82 n107 n118
  have u13_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c32802 h h0 hv n82 n118 n107
  have u14_289 : Q {2, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 u3_309 u7_114 u13_198 hv
  have u15_162 : Q {0, 2, 5, 8} := by
    by_contra hv
    exact c31443 h u2_177 u12_141 u0_29 u1_200 hv u13_198 u11_196
  have u16_187 : Q {0, 4, 5, 8} := by
    by_contra hv
    exact c32753 h h0 u13_198 u11_196 u12_141 u2_177 hv
  have u17_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c31598 h h0 u14_289 hv u13_198 u3_309
  have u18_21 : ¬ T {0, 3, 9} := by
    intro hv
    exact c25335 h u14_289 hv u4_51
  have u19_90 : T {3, 4, 9} := by
    by_contra hv
    exact c25430 h u14_289 u18_21 u5_49 hv
  have u20_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c7647 h u15_162 hv u6_105 u10_109
  have u21_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c7557 h u15_162 hv u19_90
  have u22_63 : T {1, 7, 9} := by
    by_contra hv
    exact c7592 h u15_162 u20_52 u21_59 hv
  have u23_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c11061 h u16_187 u22_63 hv
  have u24_12 : T {0, 2, 6} := by
    by_contra hv
    exact c20500 h u17_254 hv u23_67 n82
  exact c20427 h u17_254 u24_12 u19_90

theorem c32804 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n118 n107
  have u0_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u3_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  have u4_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u5_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u6_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u7_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u8_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv n118
  have u9_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31739 h h0 hv n107 n118
  have u10_113 : T {5, 6, 9} := by
    by_contra hv
    exact c31735 h h0 hv n107 n118
  have u11_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31704 h h0 hv u8_103 u7_114
  have u12_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c16071 h hv u0_29 u8_103 u7_114
  have u13_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c31777 h h0 hv u9_119
  have u14_192 : ¬ Q {0, 4, 7, 8} := by
    intro hv
    exact c31837 h h0 hv u10_113
  have u15_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u1_49 u11_112
  have u16_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4008 h hv u3_93 u11_112 u2_116
  have u17_82 : T {2, 6, 9} := by
    by_contra hv
    exact c32803 h h0 hv n118 n107
  have u18_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c9073 h hv u17_82 u10_113 u9_119
  have u19_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3219 h hv u17_82 u8_103
  have u20_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2795 h hv u17_82 u7_114
  have u21_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32801 h h0 u18_172 hv u16_136 u14_192 u13_186 u15_157
  have u22_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c361 h u21_193 u16_136 u15_157 u18_172 u13_186 hv u14_192
  have u23_78 : T {2, 5, 8} := by
    by_contra hv
    exact c12012 h u21_193 hv u3_93 u11_112
  have u24_57 : T {1, 5, 8} := by
    by_contra hv
    exact c12010 h u21_193 hv u3_93 u11_112
  have u25_40 : T {1, 2, 6} := by
    by_contra hv
    exact c11886 h u21_193 hv u3_93
  have u26_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c31848 h h0 hv u21_193 u25_40
  have u27_43 : T {1, 2, 9} := by
    by_contra hv
    exact c11328 h u22_189 hv u3_93
  have u28_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c31810 h h0 u22_189 hv u27_43
  have u29_183 : ¬ Q {0, 3, 7, 9} := by
    intro hv
    exact c10493 h hv u4_51 u23_78
  have u30_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8903 h hv u24_57 u23_78 u7_114
  have u31_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10039 h hv u24_57 u23_78 u8_103
  have u32_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9333 h hv u24_57 u23_78 u7_114
  have u33_182 : ¬ Q {0, 3, 7, 8} := by
    intro hv
    exact c10421 h hv u25_40 u5_72 u17_82
  have u34_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9573 h hv u25_40 u5_72 u17_82
  have u35_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c585 h hv u26_39
  have u36_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9082 h hv u26_39 n118
  have u37_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c630 h hv u28_42
  have u38_170 : ¬ Q {0, 3, 4, 5} := by
    intro hv
    exact c8666 h hv u28_42 n118
  have u39_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c276 h hv u19_131 u18_172 u34_176 u31_179 u33_182 u29_183
  have u40_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c272 h hv u19_131 u39_152 u18_172 u34_176 u31_179 u33_182 u29_183
  have u41_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c231 h hv u20_128 u38_170 u30_171 u18_172 u36_173 u32_174
  have u42_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c227 h hv u20_128 u41_149 u38_170 u30_171 u18_172 u36_173 u32_174
  have u43_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c14966 h hv u40_19 u11_112
  have u44_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16222 h hv u42_16 u11_112
  exact c31390 h u12_222 u27_43 u37_225 u44_224 u43_215 u6_210 u35_219

theorem c32805 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 2, 4, 7} → ¬ Q {0, 3, 4, 7} → ¬ Q {0, 1, 4, 7} → T {6, 8, 9} → T {2, 6, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n157 n172 n136 a119 a82 n107
  have u0_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u3_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c32785 h h0 hv
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u5_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u6_51 : T {1, 4, 6} := by
    by_contra hv
    exact c32784 h h0 hv
  have u7_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u8_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u9_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c32795 h h0 hv
  have u10_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c32639 h h0 hv
  have u11_118 : T {6, 7, 9} := by
    by_contra hv
    exact c32804 h h0 hv n107
  have u12_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31722 h h0 hv u7_105 u11_118
  have u13_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31632 h h0 hv u11_118
  have u14_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31630 h h0 hv a119
  have u15_101 : T {4, 5, 6} := by
    by_contra hv
    exact c31647 h h0 u14_102 hv u13_103
  have u16_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23469 h hv u6_51 u15_101 u7_105
  have u17_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31639 h h0 n107 hv
  have u18_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31705 h h0 u4_116 u13_103 hv
  have u19_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22075 h hv u5_29 u18_112 u17_114
  have u20_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u18_112
  have u21_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31667 h h0 u14_102 hv u20_109
  have u22_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22627 h hv u1_24 u7_105 u21_108
  have u23_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c32665 h h0 u22_269 hv u2_154 u3_274 u19_265 u16_275
  have u24_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4048 h hv u23_70 u12_111
  have u25_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5028 h hv u23_70 u14_102
  have u26_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3411 h hv u0_72 u15_101 u7_105
  have u27_134 : ¬ Q {0, 1, 4, 5} := by
    intro hv
    exact c3735 h hv a82 u11_118 a119
  have u28_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c3035 h hv a82 u11_118 a119
  have u29_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c31777 h h0 hv a119
  have u30_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2795 h hv a82 u17_114
  have u31_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31847 h h0 hv u18_112
  have u32_110 : T {4, 8, 9} := by
    by_contra hv
    exact c31645 h h0 hv u12_111
  have u33_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2324 h hv u9_93 u13_103 u4_116
  have u34_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5004 h hv u9_93 u13_103 u4_116
  have u35_192 : Q {0, 4, 7, 8} := by
    by_contra hv
    exact c32801 h h0 n172 u31_193 n136 hv u29_186 n157
  have u36_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c359 h u35_192 n136 n157 n172 u29_186 hv u31_193
  have u37_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c11751 h u35_192 hv a82
  have u38_76 : T {2, 5, 6} := by
    by_contra hv
    exact c11754 h u35_192 u8_49 hv
  have u39_97 : T {3, 6, 9} := by
    by_contra hv
    exact c11852 h u35_192 u8_49 u23_70 hv
  have u40_61 : ¬ T {1, 6, 9} := by
    intro hv
    exact c11875 h u35_192 hv a82 u39_97
  have u41_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u36_189 u8_49 hv
  have u42_100 : T {3, 8, 9} := by
    by_contra hv
    exact c11432 h u36_189 u8_49 u23_70 hv
  have u43_66 : T {2, 3, 5} := by
    by_contra hv
    exact c11414 h u36_189 u37_45 hv u9_93
  have u44_85 : T {2, 8, 9} := by
    by_contra hv
    exact c11330 h u36_189 u37_45 hv
  have u45_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3295 h hv u38_76 u15_101 u18_112
  have u46_138 : ¬ Q {0, 1, 4, 9} := by
    intro hv
    exact c4213 h hv u43_66 u38_76 u41_78
  have u47_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c1955 h hv u39_97 u17_114
  have u48_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c903 h hv u40_61
  have u49_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4455 h hv u44_85 u42_100 u32_110
  have u50_130 : Q {0, 1, 3, 6} := by
    by_contra hv
    exact c31533 h h0 u28_129 u26_132 u30_128 u10_133 u45_131 hv
  have u51_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c40 h hv u47_122 u30_128 u27_134 n136 u24_137 u46_138
  exact c66 h u50_130 u33_124 u51_135 u49_139 u34_143 u25_144 u48_145

end BorsukNine.FiniteObstruction

end OAI
