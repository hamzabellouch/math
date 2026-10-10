import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases084

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c31303 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 7, 9} → Q {0, 1, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro a255 a140 a159 n96
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u2_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u5_4 : T {0, 1, 5} := by
    by_contra hv
    exact c56 h a140 hv
  have u6_6 : T {0, 1, 7} := by
    by_contra hv
    exact c84 h a140 hv
  have u7_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26047 h hv u0_2 u5_4 u6_6
  have u8_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u9_26 : T {0, 4, 9} := by
    by_contra hv
    exact c380 h a159 hv
  have u10_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u11_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u12_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1440 h hv n96
  have u13_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c20563 h a255 u4_9 hv
  have u14_32 : T {0, 6, 8} := by
    by_contra hv
    exact c20698 h a255 hv n96 u13_106
  have u15_81 : T {2, 6, 8} := by
    by_contra hv
    exact c20700 h a255 hv n96 u13_106
  have u16_119 : T {6, 8, 9} := by
    by_contra hv
    exact c4584 h a140 n96 u13_106 hv
  have u17_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20581 h a255 u14_32 hv
  have u18_226 : ¬ Q {1, 3, 4, 5} := by
    intro hv
    exact c16605 h hv u14_32 u15_81 u16_119
  have u19_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16901 h hv u14_32 u15_81 u16_119
  have u20_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c20571 h a255 hv u15_81
  have u21_203 : Q {0, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 hv u7_294 u12_314 u16_119
  have u22_33 : T {0, 6, 9} := by
    by_contra hv
    exact c495 h u21_203 hv
  have u23_36 : T {0, 8, 9} := by
    by_contra hv
    exact c538 h u21_203 hv
  have u24_259 : Q {1, 6, 8, 9} := by
    by_contra hv
    exact c1774 h u21_203 hv u7_294 u12_314 u3_324 u2_328 u1_330
  have u25_206 : ¬ Q {1, 2, 3, 5} := by
    intro hv
    exact c13757 h hv u9_26 u22_33 u23_36
  have u26_208 : ¬ Q {1, 2, 3, 7} := by
    intro hv
    exact c14039 h hv u9_26 u22_33 u23_36
  have u27_233 : ¬ Q {1, 3, 5, 8} := by
    intro hv
    exact c17535 h hv u10_15 u9_26 u22_33
  have u28_238 : ¬ Q {1, 3, 7, 8} := by
    intro hv
    exact c18237 h hv u10_15 u9_26 u22_33
  have u29_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17257 h hv u10_15 u9_26 u23_36
  have u30_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c17817 h hv u10_15 u9_26 u23_36
  have u31_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c21143 h u24_259 u4_9 u11_10 hv
  have u32_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c21145 h u24_259 u4_9 u11_10 hv
  have u33_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21214 h u24_259 u20_16 u17_65 hv
  have u34_88 : T {3, 4, 7} := by
    by_contra hv
    exact c21216 h u24_259 u20_16 u17_65 hv
  have u35_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18324 h hv u31_11 u13_106
  have u36_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17626 h hv u32_13 u13_106
  have u37_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c13379 h u21_203 hv u33_86 u34_88
  have u38_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c694 h hv u26_208 u19_228 u8_232 u30_235 u28_238 u35_239
  have u39_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c664 h hv u25_206 u18_226 u29_231 u8_232 u27_233 u36_234
  have u40_45 : ¬ T {1, 3, 5} := by
    intro hv
    exact c662 h hv u39_129 u25_206 u18_226 u29_231 u8_232 u27_233 u36_234
  have u41_47 : T {1, 3, 7} := by
    by_contra hv
    exact c13316 h u21_203 u37_44 u40_45 hv
  exact c692 h u41_47 u38_131 u26_208 u19_228 u8_232 u30_235 u28_238 u35_239

private theorem c31304 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → ¬ T {0, 2, 5} → T {4, 6, 8} → Q {1, 4, 5, 7} → ¬ T {3, 6, 8} → False := by
  classical
  intro a117 n11 a106 a242 n96
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_249 : ¬ Q {1, 4, 7, 9} := by
    intro hv
    exact c19724 h hv n11 n96
  have u3_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h a242 u1_9 hv
  have u4_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16782 h hv n11 u3_119
  have u5_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 a106 hv
  have u6_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1809 h u0_121 hv a117
  have u7_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c1903 h u0_121 a106 hv a117
  have u8_116 : T {5, 8, 9} := by
    by_contra hv
    exact c1890 h u0_121 u6_104 u5_115 hv
  have u9_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1886 h u0_121 u6_104 hv u5_115
  have u10_213 : ¬ Q {1, 2, 4, 7} := by
    intro hv
    exact c14804 h hv n96 u7_112 u3_119
  have u11_136 : ¬ Q {0, 1, 4, 7} := by
    intro hv
    exact c4024 h hv n96 u7_112 u3_119
  have u12_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c19163 h hv u1_9 u8_116
  have u13_248 : ¬ Q {1, 4, 7, 8} := by
    intro hv
    exact c19583 h hv u1_9 u9_113
  exact c775 h a242 u11_136 u10_213 u4_228 u12_245 u13_248 u2_249

private theorem c31305 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {0, 2, 5} → ¬ Q {1, 2, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n11 n217 a159 n96
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u4_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_140 : Q {0, 1, 5, 7} := by
    by_contra hv
    exact c31302 h h0 hv n217 a159 n96
  have u7_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u8_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u9_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u1_9 u7_10 u8_15
  have u10_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u1_9 u7_10 u8_15
  have u11_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u12_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c31303 h h0 hv u6_140 a159 n96
  have u13_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c829 h u6_140 n217 u11_232 hv u10_251 u9_254 u12_255
  have u14_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h u13_242 u1_9 hv
  have u15_32 : T {0, 6, 8} := by
    by_contra hv
    exact c18862 h u13_242 hv n96 u14_119
  have u16_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c18757 h u13_242 u15_32 hv
  have u17_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c1038 h hv u16_70
  have u18_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c18767 h u13_242 u1_9 hv u8_15
  have u19_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c200 h hv u18_14
  have u20_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c18765 h u13_242 u1_9 hv u8_15
  have u21_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c170 h hv u20_12
  have u22_106 : T {4, 6, 8} := by
    by_contra hv
    exact c4584 h u6_140 n96 hv u14_119
  have u23_4 : T {0, 1, 5} := by
    by_contra hv
    exact c56 h u6_140 hv
  have u24_6 : T {0, 1, 7} := by
    by_contra hv
    exact c84 h u6_140 hv
  have u25_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24223 h hv u0_2 u23_4 u24_6
  have u26_56 : T {1, 5, 7} := by
    by_contra hv
    exact c7132 h a159 hv n96
  have u27_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u28_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c155 h hv n11
  have u29_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c31304 h h0 hv n11 u22_106 u13_242 n96
  have u30_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1808 h u2_121 hv u29_117
  have u31_45 : T {1, 3, 5} := by
    by_contra hv
    exact c7122 h a159 hv u29_117
  have u32_60 : T {1, 6, 8} := by
    by_contra hv
    exact c7248 h a159 hv n96 u29_117
  have u33_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6157 h hv u32_60 u30_104
  have u34_57 : ¬ T {1, 5, 8} := by
    intro hv
    exact c7155 h a159 u31_45 u26_56 hv
  have u35_55 : ¬ T {1, 5, 6} := by
    intro hv
    exact c7151 h a159 u31_45 hv u26_56
  have u36_149 : Q {0, 2, 3, 4} := by
    by_contra hv
    exact c124 h u2_121 hv u28_150 u21_151 u33_152 u19_153 u17_154
  have u37_58 : T {1, 5, 9} := by
    by_contra hv
    exact c5746 h u36_149 u35_55 u34_57 hv
  have u38_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31297 h h0 u29_117 u36_149 hv u26_56 a159 u27_301 u14_119
  have u39_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11505 h hv u31_45 u26_56 u37_58
  exact c1581 h u38_246 u39_190 u25_281 u27_301 u5_317 u4_322 u3_324

theorem c31306 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 2, 5, 7} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n217 a159 n96
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u6_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u7_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u8_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u1_9 u6_10 u7_15
  have u9_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u1_9 u6_10 u7_15
  have u10_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u11_140 : Q {0, 1, 5, 7} := by
    by_contra hv
    exact c31302 h h0 hv n217 a159 n96
  have u12_4 : T {0, 1, 5} := by
    by_contra hv
    exact c56 h u11_140 hv
  have u13_6 : T {0, 1, 7} := by
    by_contra hv
    exact c84 h u11_140 hv
  have u14_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24223 h hv u0_2 u12_4 u13_6
  have u15_255 : ¬ Q {1, 5, 7, 9} := by
    intro hv
    exact c31303 h h0 hv u11_140 a159 n96
  have u16_242 : Q {1, 4, 5, 7} := by
    by_contra hv
    exact c829 h u11_140 n217 u5_232 hv u9_251 u8_254 u15_255
  have u17_119 : ¬ T {6, 8, 9} := by
    intro hv
    exact c18743 h u16_242 u1_9 hv
  have u18_106 : T {4, 6, 8} := by
    by_contra hv
    exact c4584 h u11_140 n96 hv u17_119
  have u19_11 : T {0, 2, 5} := by
    by_contra hv
    exact c31305 h h0 hv n217 a159 n96
  have u20_246 : ¬ Q {1, 4, 6, 8} := by
    intro hv
    exact c19325 h hv u1_9 u19_11 u7_15
  have u21_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c1579 h hv u20_246 u14_281 u10_301 u4_317 u3_322 u2_324
  exact c1577 h u18_106 u21_190 u20_246 u14_281 u10_301 u4_317 u3_322 u2_324

theorem c31307 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 6, 8} → T {4, 6, 8} → ¬ Q {3, 4, 6, 8} → ¬ Q {0, 4, 6, 8} → False := by
  classical
  intro n246 a106 n301 n190
  have u0_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u1_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c1577 h a106 n190 n246 hv n301 u0_317 u1_322 u2_324
  exact c1583 h u3_281 n190 n246 n301 u0_317 u1_322 u2_324

theorem c31308 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro n119 a159 n96
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u5_217 : Q {1, 2, 5, 7} := by
    by_contra hv
    exact c31306 h h0 hv a159 n96
  have u6_41 : T {1, 2, 7} := by
    by_contra hv
    exact c609 h u5_217 hv
  have u7_39 : T {1, 2, 5} := by
    by_contra hv
    exact c581 h u5_217 hv
  have u8_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11483 h hv u1_37 u7_39 u6_41
  have u9_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1113 h a159 hv
  have u10_26 : T {0, 4, 9} := by
    by_contra hv
    exact c380 h a159 hv
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u12_301 : ¬ Q {3, 4, 6, 8} := by
    intro hv
    exact c1434 h hv n96
  have u13_16 : T {0, 3, 4} := by
    by_contra hv
    exact c15242 h u5_217 hv n119
  have u14_32 : T {0, 6, 8} := by
    by_contra hv
    exact c15360 h u5_217 hv n96 n119
  have u15_106 : T {4, 6, 8} := by
    by_contra hv
    exact c15364 h u5_217 n96 hv n119
  have u16_23 : ¬ T {0, 4, 6} := by
    intro hv
    exact c15273 h u5_217 u13_16 hv u10_26
  have u17_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c15257 h u5_217 u14_32 hv
  have u18_115 : ¬ T {5, 7, 9} := by
    intro hv
    exact c1813 h u0_121 u15_106 hv
  have u19_199 : ¬ Q {0, 5, 7, 9} := by
    intro hv
    exact c12723 h hv u1_37 u15_106
  have u20_100 : T {3, 8, 9} := by
    by_contra hv
    exact c15250 h u5_217 u16_23 hv
  have u21_246 : Q {1, 4, 6, 8} := by
    by_contra hv
    exact c31307 h h0 hv u15_106 u12_301 u8_190
  have u22_51 : T {1, 4, 6} := by
    by_contra hv
    exact c763 h u21_246 hv
  have u23_60 : T {1, 6, 8} := by
    by_contra hv
    exact c894 h u21_246 hv
  have u24_281 : Q {2, 4, 6, 8} := by
    by_contra hv
    exact c1581 h u21_246 u8_190 hv u12_301 u4_317 u3_322 u2_324
  have u25_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c19309 h u21_246 u11_15 hv
  have u26_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7411 h hv u22_51 u20_100
  have u27_176 : ¬ Q {0, 3, 5, 7} := by
    intro hv
    exact c9517 h hv u23_60 u9_75
  have u28_72 : T {2, 4, 6} := by
    by_contra hv
    exact c1078 h u24_281 hv
  have u29_28 : T {0, 5, 7} := by
    by_contra hv
    exact c19422 h u21_246 hv u25_92 u18_115
  have u30_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4471 h hv u28_72 u20_100
  have u31_70 : ¬ T {2, 3, 9} := by
    intro hv
    exact c19317 h u21_246 u29_28 hv
  have u32_49 : ¬ T {1, 3, 9} := by
    intro hv
    exact c24217 h u24_281 u29_28 hv
  have u33_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c12270 h hv u32_49 u31_70 u17_90
  have u34_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c12690 h hv u32_49 u31_70 u17_90
  have u35_186 : ¬ Q {0, 4, 5, 7} := by
    intro hv
    exact c415 h hv u30_140 u26_161 u27_176 u33_195 u34_198 u19_199
  exact c407 h u29_28 u30_140 u26_161 u27_176 u35_186 u33_195 u34_198 u19_199

end BorsukNine.FiniteObstruction

end OAI
