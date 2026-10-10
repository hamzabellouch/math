import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases128

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32707 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 4, 6, 7} → T {1, 5, 8} → T {4, 6, 7} → ¬ T {0, 5, 8} → False := by
  classical
  intro n300 a57 a105 n29
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 u0_49
  have u2_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 u1_280 n300 hv a105
  have u3_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31555 h h0 u2_189 n300 u1_280 hv
  have u4_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c11337 h u2_189 a57 hv
  exact c19176 h u3_245 n29 u4_70

theorem c32708 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → T {1, 2, 9} → False := by
  classical
  intro n224 n222 n225 n219 n127 a43
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c638 h hv n127 u0_210 n219 n222 n224 n225
  exact c31390 h n222 a43 n225 n224 u1_215 u0_210 n219

private theorem c32709 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 5, 8} → T {5, 6, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro a57 a112 n29
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32703 h h0 hv a112 n29
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u3_105 hv
  have u5_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u6_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13852 h hv n29 u5_109
  have u7_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 u0_49
  have u8_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv n29
  have u9_300 : Q {3, 4, 6, 7} := by
    by_contra hv
    exact c32707 h h0 hv a57 u3_105 n29
  have u10_88 : T {3, 4, 7} := by
    by_contra hv
    exact c1316 h u9_300 hv
  have u11_78 : T {2, 5, 8} := by
    by_contra hv
    exact c26982 h u9_300 n29 hv u4_116
  have u12_43 : T {1, 2, 9} := by
    by_contra hv
    exact c26876 h u9_300 n29 hv
  have u13_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c26875 h u9_300 hv a57
  have u14_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2647 h hv u10_88 a112
  have u15_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c26869 h u9_300 hv u11_78
  have u16_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c27857 h hv u1_24 u12_43
  have u17_42 : ¬ T {1, 2, 8} := by
    intro hv
    exact c32416 h h0 hv u9_300 u12_43
  have u18_39 : ¬ T {1, 2, 5} := by
    intro hv
    exact c32415 h h0 hv u9_300 u12_43
  have u19_30 : T {0, 5, 9} := by
    by_contra hv
    exact c26914 h u9_300 u15_8 u13_15 hv
  have u20_36 : T {0, 8, 9} := by
    by_contra hv
    exact c26916 h u9_300 u15_8 u13_15 hv
  have u21_252 : Q {1, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 hv u16_307 u8_196 a112
  have u22_287 : Q {2, 5, 6, 8} := by
    by_contra hv
    exact c31587 h h0 u21_252 u16_307 u8_196 hv
  have u23_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15623 h hv u1_24 u10_88 u3_105
  have u24_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16473 h hv u1_24 u10_88 u3_105
  have u25_221 : ¬ Q {1, 2, 6, 8} := by
    intro hv
    exact c626 h hv u17_42
  have u26_175 : ¬ Q {0, 3, 5, 6} := by
    intro hv
    exact c9366 h hv u17_42 u5_109
  have u27_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c579 h hv u18_39
  have u28_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c10064 h hv u18_39 u5_109
  have u29_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c20157 h u21_252 u1_24 hv
  have u30_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c20259 h u21_252 u1_24 hv u10_88
  have u31_21 : T {0, 3, 9} := by
    by_contra hv
    exact c20154 h u21_252 hv u30_73
  have u32_84 : T {2, 7, 9} := by
    by_contra hv
    exact c20228 h u21_252 u13_15 u29_70 hv
  have u33_75 : T {2, 4, 9} := by
    by_contra hv
    exact c20226 h u21_252 u13_15 u29_70 hv
  have u34_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c25159 h u22_287 u1_24 hv u10_88
  have u35_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19176 h hv n29 u29_70
  have u36_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3064 h hv u30_73 u4_116
  have u37_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15719 h hv u31_21 u19_30 u20_36
  have u38_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c14597 h hv u31_21 u19_30 u20_36
  have u39_171 : ¬ Q {0, 3, 4, 6} := by
    intro hv
    exact c8813 h hv a57 u32_84
  have u40_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c9937 h hv a57 u33_75
  have u41_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6004 h hv u34_52 u4_116
  have u42_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c31281 h h0 u7_280 u35_245 u3_105 hv
  have u43_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c271 h hv u36_130 u41_151 u39_171 u26_175 u40_179 u28_180
  have u44_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c257 h hv u36_130 u41_151 u39_171 u26_175 u40_179 u28_180 u43_181
  have u45_93 : ¬ T {3, 5, 8} := by
    intro hv
    exact c11439 h u42_189 a57 u11_78 hv
  have u46_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2232 h hv u45_93 u5_109
  have u47_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c601 h hv u46_124 u6_207 u38_212 u27_216 u37_220 u25_221
  have u48_224 : Q {1, 2, 7, 9} := by
    by_contra hv
    exact c32708 h h0 hv u47_222 u24_225 u23_219 u14_127 u12_43
  have u49_215 : Q {1, 2, 4, 9} := by
    by_contra hv
    exact c644 h u48_224 u14_127 u2_210 hv u23_219 u47_222 u24_225
  have u50_103 : T {4, 5, 8} := by
    by_contra hv
    exact c16226 h u48_224 u44_18 hv
  have u51_114 : T {5, 7, 8} := by
    by_contra hv
    exact c15072 h u49_215 n29 u45_93 hv
  exact c31704 h h0 a112 u50_103 u51_114

theorem c32710 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 3, 4, 9} → ¬ Q {2, 3, 6, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 3, 8, 9} → T {2, 3, 9} → False := by
  classical
  intro n265 n272 n269 n275 a70
  have u0_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u1_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u2_274 : ¬ Q {2, 3, 7, 9} := by
    intro hv
    exact c1049 h hv u1_154 u0_210 n265 n269 n272 n275
  exact c32665 h h0 n269 a70 u1_154 u2_274 n265 n275

theorem c32711 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ T {0, 5, 8} → False := by
  classical
  intro a112 n29
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u4_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 u0_49
  have u5_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv n29
  have u6_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u7_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13852 h hv n29 u6_109
  have u8_105 : T {4, 6, 7} := by
    by_contra hv
    exact c32703 h h0 hv a112 n29
  have u9_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 u8_105 hv
  have u10_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c32709 h h0 hv a112 n29
  have u11_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c851 h hv u10_57
  have u12_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26980 h hv n29 u10_57 u9_116
  have u13_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22780 h hv n29 u10_57 u9_116
  have u14_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21644 h hv n29 u10_57 u9_116
  have u15_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c6012 h hv u10_57 u6_109
  have u16_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 u11_252 hv u5_196 a112
  have u17_189 : Q {0, 4, 6, 7} := by
    by_contra hv
    exact c32616 h h0 u4_280 u12_300 hv u8_105
  have u18_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1391 h u16_307 hv
  have u19_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c27857 h u16_307 u1_24 hv
  have u20_287 : Q {2, 5, 6, 8} := by
    by_contra hv
    exact c31589 h h0 u16_307 u11_252 u5_196 hv
  have u21_23 : T {0, 4, 6} := by
    by_contra hv
    exact c341 h u17_189 hv
  have u22_245 : Q {1, 4, 6, 7} := by
    by_contra hv
    exact c31555 h h0 u17_189 u12_300 u4_280 hv
  have u23_70 : T {2, 3, 9} := by
    by_contra hv
    exact c11336 h u17_189 u10_57 hv
  have u24_64 : T {1, 8, 9} := by
    by_contra hv
    exact c11376 h u17_189 u19_43 u0_49 hv
  have u25_58 : T {1, 5, 9} := by
    by_contra hv
    exact c11374 h u17_189 u19_43 u0_49 hv
  have u26_51 : T {1, 4, 6} := by
    by_contra hv
    exact c761 h u22_245 hv
  have u27_52 : T {1, 4, 7} := by
    by_contra hv
    exact c776 h u22_245 hv
  have u28_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c19169 h u22_245 hv u18_93
  have u29_69 : ¬ T {2, 3, 8} := by
    intro hv
    exact c32016 h h0 hv u22_245 u23_70
  have u30_66 : ¬ T {2, 3, 5} := by
    intro hv
    exact c32015 h h0 hv u22_245 u23_70
  have u31_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22111 h hv u1_24 u24_64
  have u32_271 : ¬ Q {2, 3, 6, 8} := by
    intro hv
    exact c22813 h hv u1_24 u25_58
  have u33_275 : ¬ Q {2, 3, 8, 9} := by
    intro hv
    exact c23465 h hv u21_23 u26_51 u8_105
  have u34_269 : ¬ Q {2, 3, 5, 9} := by
    intro hv
    exact c22615 h hv u21_23 u26_51 u8_105
  have u35_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c25159 h u20_287 u1_24 u27_52 hv
  have u36_73 : ¬ T {2, 4, 7} := by
    intro hv
    exact c27959 h u16_307 u1_24 u27_52 hv
  have u37_84 : T {2, 7, 9} := by
    by_contra hv
    exact c27952 h u16_307 u28_15 u19_43 hv
  have u38_75 : T {2, 4, 9} := by
    by_contra hv
    exact c27950 h u16_307 u28_15 u19_43 hv
  have u39_139 : ¬ Q {0, 1, 5, 6} := by
    intro hv
    exact c4326 h hv u29_69 u6_109
  have u40_144 : ¬ Q {0, 1, 6, 8} := by
    intro hv
    exact c5024 h hv u30_66 u6_109
  have u41_272 : ¬ Q {2, 3, 6, 9} := by
    intro hv
    exact c1006 h hv u15_151 u7_207 u14_262 u31_266 u13_270 u32_271
  have u42_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2224 h hv u35_88 u9_116
  have u43_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c3064 h hv u36_73 u9_116
  have u44_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3779 h hv u37_84 u18_93
  have u45_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c4895 h hv u38_75 u18_93
  have u46_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c76 h hv u42_124 u43_130 u44_135 u39_139 u45_143 u40_144
  have u47_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c31254 h hv u39_139 u42_124 u43_130 u46_145 u45_143 u40_144
  have u48_265 : Q {2, 3, 4, 9} := by
    by_contra hv
    exact c32710 h h0 hv u41_272 u34_269 u33_275 u23_70
  have u49_114 : T {5, 7, 8} := by
    by_contra hv
    exact c21964 h u48_265 u47_5 hv
  have u50_274 : Q {2, 3, 7, 9} := by
    by_contra hv
    exact c1043 h u48_265 u3_154 u2_210 u34_269 u41_272 hv u33_275
  have u51_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31704 h h0 a112 hv u49_114
  exact c23226 h u50_274 u47_5 u51_103

theorem c32712 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → ¬ T {0, 5, 8} → False := by
  classical
  intro a105 n29
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u3_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32711 h h0 hv n29
  have u4_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c6848 h hv u0_49 u3_112
  have u5_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u3_112
  have u6_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv n29 u0_49
  have u7_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u8_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv a105 u5_109
  have u9_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv a105 u5_109
  have u10_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13773 h hv u1_24 a105 u5_109
  have u11_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14203 h hv u1_24 a105 u5_109
  have u12_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31705 h h0 u7_116 hv u3_112
  have u13_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14786 h hv n29 u3_112 u7_116
  have u14_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14086 h hv n29 u3_112 u7_116
  have u15_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21786 h hv n29 u3_112 u7_116
  have u16_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13640 h hv n29 u3_112 u7_116
  have u17_283 : ¬ Q {2, 4, 7, 8} := by
    intro hv
    exact c1612 h hv u8_108
  have u18_277 : ¬ Q {2, 4, 5, 7} := by
    intro hv
    exact c1522 h hv u9_102
  have u19_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c31535 h h0 u10_206 u11_209 u2_210 hv u14_208 u16_205
  have u20_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c1096 h hv u4_157 u13_213 u15_263 u18_277 u6_280 u17_283
  have u21_35 : ¬ T {0, 7, 9} := by
    intro hv
    exact c13859 h u19_207 hv u12_103
  have u22_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv u5_109 u20_284
  exact c519 h u22_193 u21_35

end BorsukNine.FiniteObstruction

end OAI
