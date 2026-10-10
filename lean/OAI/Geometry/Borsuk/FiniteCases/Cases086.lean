import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases013
import OAI.Geometry.Borsuk.FiniteCases.Cases085

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31309 (h : TenSystem T Q) :
    ¬ Q {0, 5, 6, 8} → ¬ Q {0, 6, 8, 9} → ¬ Q {0, 2, 6, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 4, 6, 8} → ¬ Q {0, 3, 6, 8} → T {0, 6, 8} → False := by
  classical
  intro n196 n203 n165 n201 n190 n180 a32
  have u0_144 : Q {0, 1, 6, 8} := by
    by_contra hv
    exact c467 h a32 hv n165 n180 n190 n196 n201 n203
  exact c469 h u0_144 n165 n180 n190 n196 n201 n203

theorem c31310 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 4, 9} → ¬ T {3, 6, 8} → False := by
  classical
  intro a159 n96
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
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
  have u5_314 : ¬ Q {3, 6, 8, 9} := by
    intro hv
    exact c1440 h hv n96
  have u6_180 : ¬ Q {0, 3, 6, 8} := by
    intro hv
    exact c1428 h hv n96
  have u7_10 : T {0, 2, 4} := by
    by_contra hv
    exact c150 h a159 hv
  have u8_15 : T {0, 2, 9} := by
    by_contra hv
    exact c217 h a159 hv
  have u9_75 : T {2, 4, 9} := by
    by_contra hv
    exact c1113 h a159 hv
  have u10_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c20025 h hv u4_9 u7_10 u8_15
  have u11_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20445 h hv u4_9 u7_10 u8_15
  have u12_232 : ¬ Q {1, 3, 5, 7} := by
    intro hv
    exact c31301 h hv a159
  have u13_217 : Q {1, 2, 5, 7} := by
    by_contra hv
    exact c31306 h h0 hv a159 n96
  have u14_39 : T {1, 2, 5} := by
    by_contra hv
    exact c581 h u13_217 hv
  have u15_41 : T {1, 2, 7} := by
    by_contra hv
    exact c609 h u13_217 hv
  have u16_190 : ¬ Q {0, 4, 6, 8} := by
    intro hv
    exact c11483 h hv u0_37 u14_39 u15_41
  have u17_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13307 h hv u0_37 u14_39 u15_41
  have u18_119 : T {6, 8, 9} := by
    by_contra hv
    exact c31308 h h0 hv a159 n96
  have u19_242 : ¬ Q {1, 4, 5, 7} := by
    intro hv
    exact c18743 h hv u4_9 u18_119
  have u20_294 : Q {2, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u17_203 hv u5_314 u18_119
  have u21_82 : T {2, 6, 9} := by
    by_contra hv
    exact c1230 h u20_294 hv
  have u22_85 : T {2, 8, 9} := by
    by_contra hv
    exact c1273 h u20_294 hv
  have u23_259 : Q {1, 6, 8, 9} := by
    by_contra hv
    exact c1778 h u20_294 u17_203 hv u5_314 u3_324 u2_328 u1_330
  have u24_140 : ¬ Q {0, 1, 5, 7} := by
    intro hv
    exact c4521 h hv u9_75 u21_82 u22_85
  have u25_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c21143 h u23_259 u4_9 u7_10 hv
  have u26_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c21145 h u23_259 u4_9 u7_10 hv
  have u27_255 : Q {1, 5, 7, 9} := by
    by_contra hv
    exact c831 h u13_217 u24_140 u12_232 u19_242 u10_251 u11_254 hv
  have u28_88 : T {3, 4, 7} := by
    by_contra hv
    exact c21126 h u23_259 u25_11 hv
  have u29_86 : T {3, 4, 5} := by
    by_contra hv
    exact c21128 h u23_259 u26_13 hv
  have u30_58 : T {1, 5, 9} := by
    by_contra hv
    exact c868 h u27_255 hv
  have u31_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c20563 h u27_255 u4_9 hv
  have u32_32 : T {0, 6, 8} := by
    by_contra hv
    exact c20698 h u27_255 hv n96 u31_106
  have u33_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c20581 h u27_255 u32_32 hv
  have u34_165 : ¬ Q {0, 2, 6, 8} := by
    intro hv
    exact c7979 h hv u30_58 u28_88
  have u35_44 : ¬ T {1, 3, 4} := by
    intro hv
    exact c26121 h u20_294 hv u29_86 u28_88
  have u36_90 : ¬ T {3, 4, 9} := by
    intro hv
    exact c15257 h u13_217 u32_32 hv
  have u37_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c12396 h hv u35_44 u33_65 u36_90
  have u38_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c13096 h hv u35_44 u33_65 u36_90
  exact c31309 h u37_196 u17_203 u34_165 u38_201 u16_190 u6_180 u32_32

theorem c31315 (h : TenSystem T Q) :
    ¬ Q {1, 3, 7, 8} → T {1, 3, 7} → ¬ Q {1, 3, 7, 9} → ¬ Q {1, 3, 4, 7} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 6, 7} → ¬ Q {1, 2, 3, 7} → False := by
  classical
  intro n238 a47 n239 n228 n232 n235 n208
  have u0_131 : Q {0, 1, 3, 7} := by
    by_contra hv
    exact c692 h a47 hv n208 n228 n232 n235 n238 n239
  exact c694 h u0_131 n208 n228 n232 n235 n238 n239

theorem c31320 (h : TenSystem T Q) :
    ¬ Q {1, 3, 5, 6} → ¬ Q {1, 3, 5, 7} → ¬ Q {1, 3, 5, 9} → T {1, 3, 5} → ¬ Q {1, 2, 3, 5} → ¬ Q {1, 3, 5, 8} → ¬ Q {1, 3, 4, 5} → False := by
  classical
  intro n231 n232 n234 a45 n206 n233 n226
  have u0_129 : Q {0, 1, 3, 5} := by
    by_contra hv
    exact c662 h a45 hv n206 n226 n231 n232 n233 n234
  exact c664 h u0_129 n206 n226 n231 n232 n233 n234

theorem c31322 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 4, 7, 9} → T {4, 7, 9} → ¬ Q {1, 4, 7, 9} → ¬ Q {3, 4, 7, 9} → False := by
  classical
  intro n193 a109 n249 n304
  have u0_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u1_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u2_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u3_284 : ¬ Q {2, 4, 7, 9} := by
    intro hv
    exact c1628 h hv n193 n249 n304 u2_320 u1_323 u0_325
  exact c1622 h a109 n193 n249 u3_284 n304 u2_320 u1_323 u0_325

theorem c31327 (h : TenSystem T Q) :
    ¬ Q {3, 6, 8, 9} → ¬ Q {0, 3, 6, 8} → ¬ Q {3, 6, 7, 8} → T {3, 6, 8} → ¬ Q {2, 3, 6, 8} → ¬ Q {3, 5, 6, 8} → ¬ Q {1, 3, 6, 8} → False := by
  classical
  intro n314 n180 n312 a96 n271 n307 n236
  have u0_301 : Q {3, 4, 6, 8} := by
    by_contra hv
    exact c1427 h a96 n180 n236 n271 hv n307 n312 n314
  exact c1435 h u0_301 n180 n236 n271 n307 n312 n314

theorem c31330 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → Q {0, 4, 7, 9} → ¬ T {5, 7, 9} → False := by
  classical
  intro a271 a193 n115
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1623 h a193 hv
  have u1_35 : T {0, 7, 9} := by
    by_contra hv
    exact c519 h a193 hv
  have u2_26 : T {0, 4, 9} := by
    by_contra hv
    exact c388 h a193 hv
  have u3_24 : T {0, 4, 7} := by
    by_contra hv
    exact c360 h a193 hv
  have u4_3 : T {0, 1, 4} := by
    by_contra hv
    exact c22802 h a271 hv n115
  have u5_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c22805 h a271 hv u0_109
  have u6_22 : ¬ T {0, 4, 5} := by
    intro hv
    exact c22831 h a271 u4_3 hv u3_24
  have u7_30 : T {0, 5, 9} := by
    by_contra hv
    exact c22840 h a271 u5_4 u6_22 hv
  exact c22861 h a271 u2_26 u7_30 u1_35

theorem c31335 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {0, 5, 7, 9} → False := by
  classical
  intro a115 n310 n290 n199
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_255 : Q {1, 5, 7, 9} := by
    by_contra hv
    exact c1712 h a115 n199 hv n290 n310 u0_320 u1_327 u2_329
  exact c1716 h u3_255 n199 n290 n310 u0_320 u1_327 u2_329

theorem c31342 (h : TenSystem T Q) :
    ¬ Q {2, 5, 6, 9} → ¬ Q {2, 3, 5, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {0, 2, 5, 9} → ¬ Q {2, 5, 7, 9} → T {2, 5, 9} → ¬ Q {2, 4, 5, 9} → False := by
  classical
  intro n288 n269 n291 n163 n290 a79 n279
  have u0_219 : Q {1, 2, 5, 9} := by
    by_contra hv
    exact c1172 h a79 n163 hv n269 n279 n288 n290 n291
  exact c1176 h u0_219 n163 n269 n279 n288 n290 n291

theorem c31353 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → False := by
  classical
  intro a116 n200 n311 n291
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u3_256 : Q {1, 5, 8, 9} := by
    by_contra hv
    exact c1727 h a116 n200 hv n291 n311 u0_321 u1_328 u2_329
  exact c1731 h u3_256 n200 n291 n311 u0_321 u1_328 u2_329

theorem c31365 (h : TenSystem T Q) :
    ¬ Q {1, 2, 6, 9} → ¬ Q {1, 2, 6, 7} → ¬ Q {1, 2, 3, 6} → ¬ Q {0, 1, 2, 6} → ¬ Q {1, 2, 6, 8} → ¬ Q {1, 2, 4, 6} → T {1, 2, 6} → False := by
  classical
  intro n222 n220 n207 n124 n221 n212 a40
  have u0_216 : ¬ Q {1, 2, 5, 6} := by
    intro hv
    exact c595 h hv n124 n207 n212 n220 n221 n222
  exact c587 h a40 n124 n207 n212 u0_216 n220 n221 n222

private theorem c31370 (h : TenSystem T Q) :
    ¬ Q {0, 3, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 7, 8} → T {0, 7, 8} → ¬ Q {0, 7, 8, 9} → ¬ Q {0, 1, 7, 8} → ¬ Q {0, 6, 7, 8} → False := by
  classical
  intro n182 n198 n192 a34 n204 n146 n201
  have u0_167 : Q {0, 2, 7, 8} := by
    by_contra hv
    exact c497 h a34 n146 hv n182 n192 n198 n201 n204
  exact c501 h u0_167 n146 n182 n192 n198 n201 n204

theorem c31373 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 7, 8, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 4, 7, 8} → T {0, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 1, 7, 8} → False := by
  classical
  intro n204 n198 n192 a34 n201 n146
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u2_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u5_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u6_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u7_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u8_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u9_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u10_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u11_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u12_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u13_182 : Q {0, 3, 7, 8} := by
    by_contra hv
    exact c31370 h hv n198 n192 a34 n204 n146 n201
  have u14_19 : T {0, 3, 7} := by
    by_contra hv
    exact c283 h u13_182 hv
  have u15_20 : T {0, 3, 8} := by
    by_contra hv
    exact c298 h u13_182 hv
  have u16_167 : Q {0, 2, 7, 8} := by
    by_contra hv
    exact c503 h u13_182 n146 hv n192 n198 n201 n204
  have u17_244 : ¬ Q {1, 4, 5, 9} := by
    intro hv
    exact c19055 h hv u11_9 u14_19 u15_20
  have u18_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23531 h hv u12_2 u14_19 u15_20
  have u19_279 : ¬ Q {2, 4, 5, 9} := by
    intro hv
    exact c23955 h hv u12_2 u14_19 u15_20
  have u20_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24375 h hv u12_2 u14_19 u15_20
  have u21_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25215 h hv u12_2 u14_19 u15_20
  have u22_247 : ¬ Q {1, 4, 6, 9} := by
    intro hv
    exact c19475 h hv u11_9 u14_19 u15_20
  have u23_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20315 h hv u11_9 u14_19 u15_20
  have u24_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18631 h hv u11_9 u14_19 u15_20
  have u25_13 : T {0, 2, 7} := by
    by_contra hv
    exact c193 h u16_167 hv
  have u26_14 : T {0, 2, 8} := by
    by_contra hv
    exact c208 h u16_167 hv
  have u27_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c26755 h hv u10_1 u25_13 u26_14
  have u28_296 : ¬ Q {3, 4, 5, 6} := by
    intro hv
    exact c26331 h hv u10_1 u25_13 u26_14
  have u29_302 : ¬ Q {3, 4, 6, 9} := by
    intro hv
    exact c27175 h hv u10_1 u25_13 u26_14
  have u30_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c28015 h hv u10_1 u25_13 u26_14
  have u31_188 : ¬ Q {0, 4, 5, 9} := by
    intro hv
    exact c1549 h hv u17_244 u19_279 u27_299 u1_318 u6_320 u7_321
  have u32_185 : ¬ Q {0, 4, 5, 6} := by
    intro hv
    exact c1504 h hv u24_241 u18_276 u28_296 u8_316 u9_317 u1_318
  have u33_191 : ¬ Q {0, 4, 6, 9} := by
    intro hv
    exact c1594 h hv u22_247 u20_282 u29_302 u1_318 u4_323 u5_324
  have u34_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c1684 h hv u23_253 u21_288 u30_308 u1_318 u2_327 u3_328
  have u35_104 : ¬ T {4, 5, 9} := by
    intro hv
    exact c1547 h hv u31_188 u17_244 u19_279 u27_299 u1_318 u6_320 u7_321
  have u36_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c31261 h h0 u32_185 u24_241 hv u18_276
  have u37_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1592 h hv u33_191 u22_247 u20_282 u29_302 u1_318 u4_323 u5_324
  have u38_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c1682 h hv u34_197 u23_253 u21_288 u30_308 u1_318 u2_327 u3_328
  have u39_117 : T {6, 7, 8} := by
    by_contra hv
    exact c1808 h u0_121 u35_104 hv
  have u40_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1912 h u0_121 u37_107 u38_113 hv
  have u41_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1834 h u0_121 u36_101 hv u37_107
  exact c1907 h u0_121 u41_106 u39_117 u40_119

theorem c31376 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 5, 6, 9} → T {5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → False := by
  classical
  intro n197 a113 n253 n288
  have u0_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_318 : ¬ Q {4, 5, 6, 9} := by
    intro hv
    exact c31219 h h0 hv
  have u3_308 : ¬ Q {3, 5, 6, 9} := by
    intro hv
    exact c1690 h hv n197 n253 n288 u2_318 u1_327 u0_328
  exact c1682 h a113 n197 n253 n288 u3_308 u2_318 u1_327 u0_328

end BorsukNine.FiniteObstruction

end OAI
