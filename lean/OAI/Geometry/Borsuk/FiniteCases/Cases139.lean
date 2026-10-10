import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases138

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32777 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → Q {3, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  classical
  intro a280 a300 n51
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c32747 h h0 hv
  have u4_72 : T {2, 4, 6} := by
    by_contra hv
    exact c32771 h h0 hv
  have u5_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u6_64 : T {1, 8, 9} := by
    by_contra hv
    exact c32776 h h0 hv a300 n51
  have u7_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c26871 h a300 hv u6_64
  have u8_315 : ¬ Q {3, 7, 8, 9} := by
    intro hv
    exact c28972 h hv u7_11 n51
  have u9_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c163 h hv u7_11
  have u10_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c32775 h h0 hv a300 n51
  have u11_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u12_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16473 h hv u1_24 u11_88 u0_105
  have u13_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1301 h a300 hv
  have u14_148 : ¬ Q {0, 1, 8, 9} := by
    intro hv
    exact c5685 h hv u4_72 u13_87 u0_105
  have u15_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4695 h hv u4_72 u13_87 u0_105
  have u16_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h a280 hv
  have u17_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c24071 h a280 hv u6_64
  have u18_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21247 h hv u1_24 u16_73 u11_88
  have u19_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c253 h hv u17_17
  have u20_295 : ¬ Q {2, 7, 8, 9} := by
    intro hv
    exact c26172 h hv u17_17 n51
  have u21_260 : Q {1, 7, 8, 9} := by
    by_contra hv
    exact c32772 h h0 hv u6_64 u18_259 u12_225 u14_148
  have u22_198 : Q {0, 5, 7, 8} := by
    by_contra hv
    exact c31443 h u19_177 u15_141 u2_29 u3_200 u9_162 hv u10_196
  have u23_204 : Q {0, 7, 8, 9} := by
    by_contra hv
    exact c31624 h h0 u21_260 u20_295 hv u8_315
  have u24_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1790 h u21_260 hv
  have u25_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c32157 h h0 u21_260 hv
  have u26_27 : T {0, 5, 6} := by
    by_contra hv
    exact c21308 h u21_260 u7_11 u17_17 hv
  have u27_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c21387 h u21_260 hv u4_72 u13_87
  have u28_22 : T {0, 4, 5} := by
    by_contra hv
    exact c21306 h u21_260 u7_11 u17_17 hv
  have u29_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c31897 h h0 u22_198 hv
  have u30_35 : T {0, 7, 9} := by
    by_contra hv
    exact c525 h u23_204 hv
  have u31_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13843 h hv u28_22 u24_120
  have u32_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13563 h hv u26_27 u24_120
  have u33_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31659 h h0 hv u25_101 u29_107
  have u34_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14052 h hv u27_23 u25_101 u29_107
  have u35_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14192 h hv u27_23 u25_101 u29_107
  have u36_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13719 h hv u30_35 u33_106
  exact c31535 h h0 u36_206 u35_209 u5_210 u31_207 u34_208 u32_205

theorem c32778 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → ¬ T {1, 4, 6} → False := by
  classical
  intro a300 n51
  have u0_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u1_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u4_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u5_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u6_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c765 h hv n51
  have u7_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u8_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h a300 hv
  have u9_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c26877 h a300 u2_29 hv
  have u10_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15959 h hv u2_29 u8_88
  have u11_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32777 h h0 hv a300 n51
  have u12_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u11_280 u7_245 u0_105 hv
  have u13_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u12_189 u1_49 hv
  have u14_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11328 h u12_189 u9_43 hv
  have u15_259 : Q {1, 6, 8, 9} := by
    by_contra hv
    exact c32773 h h0 u12_189 hv a300
  have u16_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19847 h hv u2_29 u13_78 u14_93
  have u17_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5179 h hv u13_78 u8_88
  have u18_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21115 h hv u2_29 u13_78 u14_93
  have u19_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c32147 h h0 u15_259 hv
  have u20_253 : Q {1, 5, 6, 9} := by
    by_contra hv
    exact c916 h u15_259 u17_145 u10_222 u3_237 u6_247 hv u18_258
  have u21_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c21247 h u15_259 u4_24 hv u8_88
  have u22_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c32087 h h0 u20_253 hv
  have u23_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c1095 h hv u21_73
  have u24_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31667 h h0 u19_102 u22_108 hv
  have u25_193 : ¬ Q {0, 4, 7, 9} := by
    intro hv
    exact c31573 h h0 hv u23_284 u16_249 u5_304
  exact c32680 h h0 u25_193 u24_109 u23_284

private theorem c32779 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 2, 9} → Q {1, 6, 8, 9} → ¬ T {1, 4, 6} → False := by
  classical
  intro n43 a259 n51
  have u0_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32742 h h0 hv
  have u4_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u5_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u6_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u7_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u8_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32778 h h0 hv n51
  have u9_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 hv u7_245 u8_300
  have u10_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u9_280 hv
  have u11_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c21247 h a259 u1_24 u10_73 hv
  have u12_11 : T {0, 2, 5} := by
    by_contra hv
    exact c21126 h a259 hv u11_88
  have u13_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c32148 h h0 a259 u12_11 hv
  have u14_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c140 h hv u13_10
  have u15_64 : T {1, 8, 9} := by
    by_contra hv
    exact c958 h a259 hv
  have u16_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c21139 h a259 u1_24 hv
  have u17_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c21133 h a259 hv u10_73
  have u18_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21222 h a259 u17_17 u16_66 hv
  have u19_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7841 h hv u15_64 u18_86
  have u20_92 : T {3, 5, 7} := by
    by_contra hv
    exact c21224 h a259 u17_17 u16_66 hv
  have u21_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c6721 h hv u15_64 u20_92
  have u22_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2224 h hv u11_88 u0_116
  have u23_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c32147 h h0 a259 hv
  have u24_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7968 h hv u6_49 u23_102
  have u25_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5881 h hv u15_64 u3_105
  have u26_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u9_280 u7_245 hv u8_300
  have u27_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u26_189 u6_49 hv
  have u28_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6144 h hv n51 u0_116
  have u29_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c765 h hv n51
  have u30_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c641 h hv n43
  have u31_93 : T {3, 5, 8} := by
    by_contra hv
    exact c11328 h u26_189 n43 hv
  have u32_58 : T {1, 5, 9} := by
    by_contra hv
    exact c11374 h u26_189 n43 u6_49 hv
  have u33_258 : ¬ Q {1, 6, 7, 9} := by
    intro hv
    exact c21115 h hv u2_29 u27_78 u31_93
  have u34_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5173 h hv u10_73 u31_93
  have u35_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8177 h hv u18_86 u20_92 u31_93
  have u36_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6295 h hv u32_58 u3_105
  have u37_253 : Q {1, 5, 6, 9} := by
    by_contra hv
    exact c916 h a259 u34_145 u30_222 u4_237 u29_247 hv u33_258
  have u38_151 : Q {0, 2, 3, 6} := by
    by_contra hv
    exact c31534 h h0 u36_153 u25_150 u14_149 u5_154 u28_152 hv
  have u39_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c32087 h h0 u37_253 hv
  have u40_160 : Q {0, 2, 5, 6} := by
    by_contra hv
    exact c171 h u38_151 u22_124 u21_156 hv u19_164 u24_165 u35_166
  exact c7268 h u40_160 u6_49 u39_108

theorem c32780 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 8, 9} → ¬ T {1, 4, 6} → False := by
  classical
  intro a259 n51
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c32720 h h0 hv
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u4_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u5_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c761 h hv n51
  have u6_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c32778 h h0 hv n51
  have u7_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32755 h h0 hv u5_245 u6_300
  have u8_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31557 h h0 u7_280 u5_245 hv u6_300
  have u9_78 : T {2, 5, 8} := by
    by_contra hv
    exact c11334 h u8_189 u0_49 hv
  have u10_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u7_280 hv
  have u11_64 : T {1, 8, 9} := by
    by_contra hv
    exact c958 h a259 hv
  have u12_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1775 h a259 hv
  have u13_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c32147 h h0 a259 hv
  have u14_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c21247 h a259 u3_24 u10_73 hv
  have u15_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c21133 h a259 hv u10_73
  have u16_43 : T {1, 2, 9} := by
    by_contra hv
    exact c32779 h h0 hv a259 n51
  have u17_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c11329 h u8_189 u16_43 hv
  have u18_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c31809 h h0 u8_189 hv u16_43
  have u19_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c31810 h h0 u8_189 hv u16_43
  have u20_58 : ¬ T {1, 5, 9} := by
    intro hv
    exact c11379 h u8_189 u16_43 hv u11_64
  have u21_8 : T {0, 1, 9} := by
    by_contra hv
    exact c24068 h u7_280 hv u17_93
  have u22_57 : T {1, 5, 8} := by
    by_contra hv
    exact c24184 h u7_280 hv u17_93 u1_116
  have u23_45 : T {1, 3, 5} := by
    by_contra hv
    exact c24154 h u7_280 u15_17 hv u17_93
  have u24_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13286 h hv u18_39 u14_88
  have u25_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10208 h hv u19_42 u13_102
  have u26_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12448 h hv u19_42 u14_88
  have u27_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c866 h hv u20_58
  have u28_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c32210 h h0 u7_280 hv u21_8
  have u29_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c22953 h hv u3_24 u22_57
  have u30_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28815 h hv u2_29 u22_57 u9_78
  have u31_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27267 h hv u2_29 u22_57 u9_78
  have u32_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26039 h hv u3_24 u23_45
  have u33_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25188 h hv u28_7 u14_88
  have u34_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u24_203 u32_294 hv u12_119
  have u35_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c31594 h h0 hv u27_253 u26_197 u33_288
  exact c1456 h u34_314 u25_181 u4_237 u29_272 u31_302 u35_308 u30_313

end BorsukNine.FiniteObstruction

end OAI
