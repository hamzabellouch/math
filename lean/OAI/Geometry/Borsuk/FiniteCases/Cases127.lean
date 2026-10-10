import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases126

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32692 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 5, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a29 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_237 : ¬ Q {1, 3, 6, 9} := by
    intro hv
    exact c32643 h h0 hv
  have u2_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u3_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u4_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u5_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c32689 h h0 hv a29 a154
  have u6_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1091 h u5_280 hv
  have u7_105 : T {4, 6, 7} := by
    by_contra hv
    exact c1567 h u5_280 hv
  have u8_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32207 h h0 u5_280 hv
  have u9_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c32212 h h0 u5_280 hv u3_21
  have u10_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4609 h hv u2_70 u7_105
  have u11_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c253 h hv u9_17
  have u12_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c32691 h h0 hv a29 a154
  have u13_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c1668 h hv u12_112
  have u14_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv u12_112
  have u15_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv u12_112
  have u16_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31709 h h0 u8_116 hv u12_112
  have u17_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31705 h h0 u8_116 hv u12_112
  have u18_207 : ¬ Q {1, 2, 3, 6} := by
    intro hv
    exact c13853 h hv a29 u14_109
  have u19_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17297 h hv u0_24 u6_73 u14_109
  have u20_236 : ¬ Q {1, 3, 6, 8} := by
    intro hv
    exact c18005 h hv u0_24 u6_73 u14_109
  have u21_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28099 h hv u0_24 u15_52 u6_73
  have u22_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c28947 h hv u0_24 u15_52 u6_73
  have u23_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c16649 h hv u4_15 u16_114
  have u24_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17769 h hv u4_15 u17_103
  have u25_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c679 h hv u18_207 u23_227 u19_231 u24_235 u20_236 u1_237
  have u26_46 : T {1, 3, 6} := by
    by_contra hv
    exact c32672 h h0 u5_280 u22_314 u21_308 u11_177 u15_52 u13_196 u10_141 hv u12_112 u14_109 a29 u2_70
  exact c677 h u26_46 u25_130 u18_207 u23_227 u19_231 u24_235 u20_236 u1_237

private theorem c32693 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → ¬ T {5, 6, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro a105 n112 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u3_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32692 h h0 hv a154
  have u4_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c31636 h h0 a105 hv
  have u5_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c6435 h a154 hv a105
  have u6_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c31670 h h0 hv a105 u2_109
  have u7_102 : ¬ T {4, 5, 7} := by
    intro hv
    exact c31666 h h0 hv a105 u2_109
  have u8_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13773 h hv u0_24 a105 u2_109
  have u9_209 : ¬ Q {1, 2, 3, 8} := by
    intro hv
    exact c14203 h hv u0_24 a105 u2_109
  have u10_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14086 h hv u3_29 n112 u4_116
  have u11_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13640 h hv u3_29 n112 u4_116
  have u12_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c24748 h hv u3_29 u5_57 n112
  have u13_55 : T {1, 5, 6} := by
    by_contra hv
    exact c6430 h a154 hv u6_108
  have u14_60 : T {1, 6, 8} := by
    by_contra hv
    exact c6438 h a154 hv u7_102
  have u15_207 : Q {1, 2, 3, 6} := by
    by_contra hv
    exact c31535 h h0 u8_206 u9_209 u1_210 hv u10_208 u11_205
  have u16_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv u2_109 u12_284
  have u17_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c11933 h u16_193 hv u13_55 u14_60
  exact c680 h u15_207 u17_46

private theorem c32694 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 4, 7, 9} → T {1, 5, 8} → T {4, 7, 9} → ¬ T {0, 5, 8} → False := by
  classical
  intro n284 a57 a109 n29
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_193 : Q {0, 4, 7, 9} := by
    by_contra hv
    exact c32680 h h0 hv a109 n284
  have u2_249 : Q {1, 4, 7, 9} := by
    by_contra hv
    exact c31573 h h0 u1_193 n284 hv u0_304
  have u3_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c11899 h u1_193 a57 hv
  exact c19738 h u2_249 n29 u3_67

private theorem c32695 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 8} → Q {0, 2, 3, 9} → False := by
  classical
  intro n112 a154
  have u0_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u1_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32692 h h0 hv a154
  have u2_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c435 h hv u1_29
  have u3_109 : T {4, 7, 9} := by
    by_contra hv
    exact c31643 h h0 hv n112
  have u4_52 : T {1, 4, 7} := by
    by_contra hv
    exact c6426 h a154 hv n112
  have u5_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c32693 h h0 hv n112 a154
  have u6_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u5_105 hv
  have u7_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u5_105
  have u8_284 : Q {2, 4, 7, 9} := by
    by_contra hv
    exact c32694 h h0 hv u7_57 u3_109 u1_29
  have u9_73 : T {2, 4, 7} := by
    by_contra hv
    exact c1095 h u8_284 hv
  have u10_46 : T {1, 3, 6} := by
    by_contra hv
    exact c24638 h u8_284 u1_29 hv
  have u11_311 : ¬ Q {3, 5, 8, 9} := by
    intro hv
    exact c28527 h hv u0_24 u4_52 u9_73
  have u12_291 : ¬ Q {2, 5, 8, 9} := by
    intro hv
    exact c25619 h hv u0_24 u10_46
  exact c31353 h h0 u6_116 u2_200 u11_311 u12_291

theorem c32696 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 9} → False := by
  classical
  intro a154
  have u0_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c32638 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u3_15 : T {0, 2, 9} := by
    by_contra hv
    exact c215 h a154 hv
  have u4_21 : T {0, 3, 9} := by
    by_contra hv
    exact c305 h a154 hv
  have u5_70 : T {2, 3, 9} := by
    by_contra hv
    exact c1038 h a154 hv
  have u6_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c20157 h hv u1_24 u5_70
  have u7_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c32692 h h0 hv a154
  have u8_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c431 h hv u7_29
  have u9_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c24076 h hv u7_29 u0_49
  have u10_112 : T {5, 6, 8} := by
    by_contra hv
    exact c32695 h h0 hv a154
  have u11_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv u10_112
  have u12_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c6427 h a154 hv u10_112
  have u13_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16789 h hv u3_15 u10_112
  have u14_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14689 h hv u4_21 u10_112
  have u15_307 : Q {3, 5, 6, 8} := by
    by_contra hv
    exact c32631 h h0 u6_252 hv u8_196 u10_112
  have u16_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c776 h hv u12_52
  have u17_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1391 h u15_307 hv
  have u18_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c27857 h u15_307 u1_24 hv
  have u19_73 : T {2, 4, 7} := by
    by_contra hv
    exact c27964 h u15_307 u12_52 hv u11_109
  have u20_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c32482 h h0 u15_307 u3_15 hv
  have u21_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c32483 h h0 u15_307 u3_15 hv
  have u22_8 : ¬ T {0, 1, 9} := by
    intro hv
    exact c27849 h u15_307 hv u19_73
  have u23_287 : Q {2, 5, 6, 8} := by
    by_contra hv
    exact c31589 h h0 u15_307 u6_252 u8_196 hv
  have u24_145 : ¬ Q {0, 1, 6, 9} := by
    intro hv
    exact c5173 h hv u19_73 u17_93
  have u25_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c637 h hv u18_43
  have u26_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26876 h hv u7_29 u18_43
  have u27_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c138 h hv u20_10
  have u28_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1166 h u23_287 hv
  have u29_88 : T {3, 4, 7} := by
    by_contra hv
    exact c25048 h u23_287 u22_8 hv
  have u30_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c32283 h h0 u23_287 hv u4_21
  have u31_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c32282 h h0 u23_287 hv u4_21
  have u32_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c31555 h h0 hv u26_300 u9_280 u16_245
  have u33_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c228 h hv u31_16
  have u34_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31281 h h0 u9_280 u16_245 hv u32_189
  have u35_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u34_105 hv
  have u36_57 : T {1, 5, 8} := by
    by_contra hv
    exact c6434 h a154 hv u34_105
  have u37_108 : T {4, 7, 8} := by
    by_contra hv
    exact c6502 h a154 u12_52 u34_105 hv
  have u38_102 : T {4, 5, 7} := by
    by_contra hv
    exact c6498 h a154 u12_52 hv u34_105
  have u39_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31710 h h0 u10_112 hv u35_116
  have u40_135 : ¬ Q {0, 1, 4, 6} := by
    intro hv
    exact c3865 h hv u28_78 u17_93 u35_116
  have u41_181 : ¬ Q {0, 3, 6, 9} := by
    intro hv
    exact c10219 h hv u36_57 u19_73
  have u42_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c13275 h hv u36_57 u28_78 u17_93
  have u43_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c11727 h hv u36_57 u28_78 u17_93
  have u44_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8119 h hv u36_57 u29_88
  have u45_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u37_108 hv
  have u46_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c31887 h h0 hv u37_108
  have u47_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c6431 h a154 hv u37_108
  have u48_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u38_102 hv
  have u49_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c31947 h h0 hv u38_102
  have u50_60 : ¬ T {1, 6, 8} := by
    intro hv
    exact c6439 h a154 hv u38_102
  have u51_51 : T {1, 4, 6} := by
    by_contra hv
    exact c6424 h a154 hv u39_114
  have u52_33 : ¬ T {0, 6, 9} := by
    intro hv
    exact c482 h hv u24_145 u44_166 u41_181 u43_191 u46_197 u42_202 u49_203
  have u53_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv u21_13 u45_113
  have u54_214 : ¬ Q {1, 2, 4, 8} := by
    intro hv
    exact c14826 h hv u30_19 u45_113
  have u55_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c819 h hv u47_55
  have u56_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16504 h hv u21_13 u48_119
  have u57_211 : ¬ Q {1, 2, 4, 5} := by
    intro hv
    exact c14404 h hv u30_19 u48_119
  have u58_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c894 h hv u50_60
  have u59_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c13574 h hv u52_33 u39_114
  have u60_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c655 h hv u33_128 u59_205 u56_226 u13_228 u53_229 u2_230
  have u61_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c565 h hv u27_122 u59_205 u57_211 u14_213 u54_214 u25_215
  have u62_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c766 h hv u40_135 u61_212 u60_227 u55_241 u16_245 u58_246
  exact c752 h u51_51 u40_135 u61_212 u60_227 u55_241 u16_245 u58_246 u62_247

theorem c32697 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → T {5, 8, 9} → ¬ Q {0, 5, 8, 9} → False := by
  classical
  intro n311 n256 a116 n200
  have u0_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31353 h h0 a116 n200 n311 hv
  exact c31606 h h0 u0_291 n256 n200 n311

theorem c32698 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 4, 7} → T {1, 5, 8} → ¬ T {1, 3, 6} → ¬ T {4, 6, 7} → T {5, 6, 8} → ¬ Q {0, 5, 8, 9} → False := by
  classical
  intro n52 a57 n46 n105 a112 n200
  have u0_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u1_24 : T {0, 4, 7} := by
    by_contra hv
    exact c32671 h h0 hv
  have u2_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c32641 h h0 hv
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c32644 h h0 hv
  have u4_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 n105 hv
  have u5_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6247 h hv a57 a112 u4_116
  have u6_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c5801 h hv a57 a112 u4_116
  have u7_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c686 h hv n46
  have u8_227 : ¬ Q {1, 3, 4, 6} := by
    intro hv
    exact c682 h hv n46
  have u9_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c31644 h h0 hv a112
  have u10_102 : T {4, 5, 7} := by
    by_contra hv
    exact c31665 h h0 hv u9_109 n105
  have u11_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c31630 h h0 u10_102 hv
  have u12_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u9_109 n105
  have u13_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31642 h h0 u12_108 hv
  have u14_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c772 h hv n52
  have u15_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c5932 h hv n52 n105 u9_109
  have u16_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c6362 h hv n52 n105 u9_109
  have u17_151 : Q {0, 2, 3, 6} := by
    by_contra hv
    exact c31534 h h0 u16_153 u15_150 u6_149 u0_154 u5_152 hv
  have u18_12 : T {0, 2, 6} := by
    by_contra hv
    exact c170 h u17_151 hv
  have u19_67 : T {2, 3, 6} := by
    by_contra hv
    exact c993 h u17_151 hv
  have u20_256 : ¬ Q {1, 5, 8, 9} := by
    intro hv
    exact c20719 h hv u1_24 u19_67
  have u21_311 : Q {3, 5, 8, 9} := by
    by_contra hv
    exact c32697 h h0 hv u20_256 u4_116 n200
  have u22_291 : Q {2, 5, 8, 9} := by
    by_contra hv
    exact c31607 h h0 hv n200 u20_256 u21_311
  have u23_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c32521 h h0 hv u18_12 u21_311
  have u24_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c32523 h h0 hv u18_12 u21_311
  have u25_78 : T {2, 5, 8} := by
    by_contra hv
    exact c1170 h u22_291 hv
  have u26_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18182 h hv u23_10 u13_113
  have u27_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c17342 h hv u23_10 u11_119
  have u28_229 : ¬ Q {1, 3, 4, 8} := by
    intro hv
    exact c16926 h hv u24_13 u13_113
  have u29_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16504 h hv u24_13 u11_119
  have u30_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3307 h hv u25_78 a112 u4_116
  have u31_128 : ¬ Q {0, 1, 3, 4} := by
    intro hv
    exact c2861 h hv u25_78 a112 u4_116
  have u32_205 : ¬ Q {1, 2, 3, 4} := by
    intro hv
    exact c651 h hv u31_128 u29_226 u8_227 u14_228 u28_229 u2_230
  have u33_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c647 h hv u31_128 u32_205 u29_226 u8_227 u14_228 u28_229 u2_230
  have u34_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c696 h hv u30_131 u14_228 u27_232 u7_235 u26_238 u3_239
  have u35_47 : T {1, 3, 7} := by
    by_contra hv
    exact c25668 h u22_291 u33_44 n46 hv
  exact c31315 h u26_238 u35_47 u3_239 u14_228 u27_232 u7_235 u34_208

end BorsukNine.FiniteObstruction

end OAI
