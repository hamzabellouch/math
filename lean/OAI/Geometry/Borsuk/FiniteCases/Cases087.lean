import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases013
import OAI.Geometry.Borsuk.FiniteCases.Cases084

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31377 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → ¬ Q {0, 2, 5, 6} → ¬ Q {0, 5, 6, 8} → ¬ Q {0, 1, 5, 6} → Q {1, 2, 3, 9} → T {5, 6, 9} → ¬ Q {1, 5, 6, 9} → ¬ Q {2, 5, 6, 9} → ¬ Q {1, 2, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a112 n160 n196 n139 a210 a113 n253 n288 n216 a120
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := h0
  have u3_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u4_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u5_317 : ¬ Q {4, 5, 6, 8} := by
    intro hv
    exact c31220 h h0 hv
  have u6_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u2_121 hv a113
  have u7_241 : ¬ Q {1, 4, 5, 6} := by
    intro hv
    exact c18603 h hv u1_9 a120
  have u8_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23503 h hv u0_2 a120
  have u9_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c1819 h u2_121 hv a112
  have u10_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c1869 h u2_121 hv a112 a113
  have u11_24 : ¬ T {0, 4, 7} := by
    intro hv
    exact c14267 h a210 hv a112
  have u12_266 : ¬ Q {2, 3, 5, 6} := by
    intro hv
    exact c22198 h hv u11_24 u6_108 u9_109
  have u13_231 : ¬ Q {1, 3, 5, 6} := by
    intro hv
    exact c17298 h hv u11_24 u6_108 u9_109
  have u14_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c1655 h hv u10_111
  have u15_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1657 h hv u10_111
  have u16_252 : ¬ Q {1, 5, 6, 8} := by
    intro hv
    exact c824 h hv n139 n216 u13_231 u7_241 u14_251 n253
  have u17_287 : ¬ Q {2, 5, 6, 8} := by
    intro hv
    exact c1139 h hv n160 n216 u12_266 u8_276 u15_286 n288
  have u18_307 : ¬ Q {3, 5, 6, 8} := by
    intro hv
    exact c1675 h hv n196 u16_252 u17_287 u5_317 u4_326 u3_328
  exact c1667 h a112 n196 u16_252 u17_287 u18_307 u5_317 u4_326 u3_328

theorem c31378 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 5, 6, 7} → T {5, 6, 7} → ¬ Q {1, 5, 6, 7} → ¬ Q {0, 5, 6, 7} → False := by
  classical
  intro n286 a111 n251 n195
  have u0_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u3_306 : Q {3, 5, 6, 7} := by
    by_contra hv
    exact c1652 h a111 n195 n251 n286 hv u0_316 u1_326 u2_327
  exact c1660 h u3_306 n195 n251 n286 u0_316 u1_326 u2_327

theorem c31390 (h : TenSystem T Q) :
    ¬ Q {1, 2, 6, 9} → T {1, 2, 9} → ¬ Q {1, 2, 8, 9} → ¬ Q {1, 2, 7, 9} → ¬ Q {1, 2, 4, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 2, 5, 9} → False := by
  classical
  intro n222 a43 n225 n224 n215 n210 n219
  have u0_127 : Q {0, 1, 2, 9} := by
    by_contra hv
    exact c632 h a43 hv n210 n215 n219 n222 n224 n225
  exact c634 h u0_127 n210 n215 n219 n222 n224 n225

theorem c31392 (h : TenSystem T Q) :
    ¬ Q {1, 3, 6, 9} → ¬ Q {1, 2, 3, 9} → ¬ Q {1, 3, 4, 9} → ¬ Q {1, 3, 5, 9} → T {1, 3, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 3, 7, 9} → False := by
  classical
  intro n237 n210 n230 n234 a49 n240 n239
  have u0_133 : Q {0, 1, 3, 9} := by
    by_contra hv
    exact c722 h a49 hv n210 n230 n234 n237 n239 n240
  exact c724 h u0_133 n210 n230 n234 n237 n239 n240

private theorem c31396 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {7, 8, 9} → T {5, 6, 9} → Q {1, 3, 7, 9} → Q {1, 3, 5, 9} → False := by
  classical
  intro a120 a113 a239 a234
  have u0_121 : Q {0, 1, 2, 3} := h0
  have u1_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u0_121 hv a113
  have u2_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u1_108
  have u3_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c18327 h a239 u2_12 hv
  have u4_118 : T {6, 7, 9} := by
    by_contra hv
    exact c1806 h u0_121 u3_103 hv
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1911 h u0_121 hv a113 u4_118
  have u6_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1814 h u0_121 u5_107 hv
  have u7_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c1803 h u0_121 hv a120
  have u8_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1925 h u0_121 u6_114 hv a120
  have u9_14 : T {0, 2, 8} := by
    by_contra hv
    exact c18328 h a239 hv u7_101
  have u10_10 : T {0, 2, 4} := by
    by_contra hv
    exact c17622 h a234 hv u8_117
  exact c17645 h a234 u10_10 u2_12 u9_14

private theorem c31397 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → Q {1, 3, 7, 9} → Q {1, 3, 5, 9} → False := by
  classical
  intro a113 a239 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u0_121 hv a113
  have u2_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv u1_108
  have u3_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c18327 h a239 u2_12 hv
  have u4_106 : T {4, 6, 8} := by
    by_contra hv
    exact c1846 h u0_121 u3_103 hv u1_108
  have u5_120 : ¬ T {7, 8, 9} := by
    intro hv
    exact c31396 h h0 hv a113 a239 a234
  have u6_101 : T {4, 5, 6} := by
    by_contra hv
    exact c1802 h u0_121 hv u5_120
  have u7_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c1831 h u0_121 u6_101 hv u4_106
  have u8_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c18329 h a239 hv u6_101
  exact c17628 h a234 u8_14 u7_105

theorem c31398 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 7, 9} → Q {1, 3, 5, 9} → False := by
  classical
  intro a239 a234
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u4_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u5_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h a239 hv
  have u6_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13315 h hv u0_37 u4_45 u5_47
  have u7_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26087 h hv u1_2 u4_45 u5_47
  have u8_113 : ¬ T {5, 6, 9} := by
    intro hv
    exact c31397 h h0 hv a239 a234
  have u9_108 : T {4, 7, 8} := by
    by_contra hv
    exact c1816 h u2_121 hv u8_113
  have u10_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17625 h a234 hv u9_108
  have u11_103 : T {4, 5, 8} := by
    by_contra hv
    exact c18326 h a239 u10_12 hv
  have u12_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u2_121 u11_103 hv
  have u13_106 : ¬ T {4, 6, 8} := by
    intro hv
    exact c1847 h u2_121 u11_103 hv u9_108
  have u14_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1916 h u2_121 u8_113 u12_118 hv
  have u15_11 : T {0, 2, 5} := by
    by_contra hv
    exact c18324 h a239 hv u13_106
  have u16_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17626 h a234 hv u13_106
  have u17_314 : Q {3, 6, 8, 9} := by
    by_contra hv
    exact c31274 h h0 u6_203 u7_294 hv u14_119
  exact c28855 h u17_314 u3_1 u15_11 u16_13

private theorem c31399 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → ¬ T {4, 6, 8} → T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro a103 n106 a108 a133 n192 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_58 : T {1, 5, 9} := by
    by_contra hv
    exact c862 h a234 hv
  have u2_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1400 h a234 hv
  have u3_115 : T {5, 7, 9} := by
    by_contra hv
    exact c1812 h u0_121 n106 hv
  have u4_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7093 h hv u1_58 u2_94 u3_115
  have u5_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h a133 hv n106
  have u6_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1851 h u0_121 a103 a108 hv
  have u7_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3569 h a133 hv a103 a108
  have u8_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c1638 h hv u6_110
  have u9_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u0_121 u6_110 hv
  have u10_25 : T {0, 4, 8} := by
    by_contra hv
    exact c17730 h a234 hv u7_74 n106
  have u11_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4147 h hv u5_77 u9_111 u3_115
  have u12_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9189 h hv u5_77 u9_111 u3_115
  have u13_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c370 h hv u11_137 u4_158 u12_173 n190 n192 u8_194
  exact c362 h u10_25 u11_137 u4_158 u12_173 u13_187 n190 n192 u8_194

private theorem c31400 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro n106 a108 a133 n192 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u2_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u3_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u4_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u5_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17626 h a234 hv n106
  have u6_77 : T {2, 5, 7} := by
    by_contra hv
    exact c3492 h a133 hv n106
  have u7_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c31399 h h0 hv n106 a108 a133 n192 n190 a234
  have u8_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1848 h u0_121 u7_103 n106 hv
  have u9_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv u7_103
  have u10_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12031 h hv u4_45 u9_80
  have u11_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19951 h hv u5_13 u6_77 u9_80
  have u12_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27675 h hv u5_13 u6_77 u9_80
  have u13_285 : ¬ Q {2, 4, 8, 9} := by
    intro hv
    exact c1643 h hv u10_194 u11_250 u12_305 u3_321 u2_324 u1_325
  exact c1637 h u8_110 u10_194 u11_250 u13_285 u12_305 u3_321 u2_324 u1_325

theorem c31401 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 4, 6, 7} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro a108 a133 n192 n292 n280 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17625 h a234 hv a108
  have u2_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c3491 h a133 hv a108
  have u3_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c176 h hv u1_12
  have u4_286 : ¬ Q {2, 5, 6, 7} := by
    intro hv
    exact c1136 h hv u2_76
  have u5_106 : T {4, 6, 8} := by
    by_contra hv
    exact c31400 h h0 hv a108 a133 n192 n190 a234
  have u6_103 : ¬ T {4, 5, 8} := by
    intro hv
    exact c1847 h u0_121 hv u5_106 a108
  have u7_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1853 h u0_121 u5_106 a108 hv
  have u8_25 : ¬ T {0, 4, 8} := by
    intro hv
    exact c17735 h a234 hv u5_106 a108
  have u9_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv u6_103
  have u10_220 : ¬ Q {1, 2, 6, 7} := by
    intro hv
    exact c15766 h hv u8_25 u6_103 u7_110
  have u11_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22766 h hv u8_25 u6_103 u7_110
  have u12_293 : ¬ Q {2, 6, 7, 9} := by
    intro hv
    exact c1201 h hv u3_164 u10_220 u11_270 n280 u4_286 n292
  exact c1187 h u9_80 u3_164 u10_220 u11_270 n280 u4_286 n292 u12_293

theorem c31402 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 4, 8, 9} → T {4, 8, 9} → ¬ Q {3, 4, 8, 9} → ¬ Q {0, 4, 8, 9} → False := by
  classical
  intro n250 a110 n305 n194
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u2_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u3_285 : Q {2, 4, 8, 9} := by
    by_contra hv
    exact c1637 h a110 n194 n250 hv n305 u0_321 u1_324 u2_325
  exact c1643 h u3_285 n194 n250 n305 u0_321 u1_324 u2_325

private theorem c31403 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → T {0, 2, 6} → ¬ T {4, 7, 8} → Q {0, 1, 3, 9} → T {1, 3, 5} → False := by
  classical
  intro n103 a12 n108 a133 a45
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_76 : T {2, 5, 6} := by
    by_contra hv
    exact c3490 h a133 hv n108
  have u2_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1850 h u0_121 n103 n108 hv
  have u3_80 : T {2, 6, 7} := by
    by_contra hv
    exact c3496 h a133 hv n103
  have u4_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c27667 h hv a12 u1_76 u3_80
  have u5_250 : ¬ Q {1, 4, 8, 9} := by
    intro hv
    exact c19943 h hv a12 u1_76 u3_80
  have u6_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c12031 h hv a45 u3_80
  exact c31402 h h0 u5_250 u2_110 u4_305 u6_194

theorem c31404 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → ¬ T {4, 7, 8} → Q {0, 1, 3, 9} → ¬ Q {0, 4, 7, 8} → ¬ Q {0, 4, 6, 8} → Q {1, 3, 5, 9} → False := by
  classical
  intro a106 n108 a133 n192 n190 a234
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_45 : T {1, 3, 5} := by
    by_contra hv
    exact c675 h a234 hv
  have u2_12 : T {0, 2, 6} := by
    by_contra hv
    exact c17624 h a234 hv n108
  have u3_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31403 h h0 hv u2_12 n108 a133 u1_45
  have u4_58 : T {1, 5, 9} := by
    by_contra hv
    exact c862 h a234 hv
  have u5_94 : T {3, 5, 9} := by
    by_contra hv
    exact c1400 h a234 hv
  have u6_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1816 h u0_121 n108 hv
  have u7_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7091 h hv u4_58 u5_94 u6_113
  have u8_76 : T {2, 5, 6} := by
    by_contra hv
    exact c3490 h a133 hv n108
  have u9_110 : ¬ T {4, 8, 9} := by
    intro hv
    exact c1849 h u0_121 u3_103 a106 hv
  have u10_74 : ¬ T {2, 4, 8} := by
    intro hv
    exact c3567 h a133 hv u3_103 a106
  have u11_194 : ¬ Q {0, 4, 8, 9} := by
    intro hv
    exact c1638 h hv u9_110
  have u12_111 : T {5, 6, 7} := by
    by_contra hv
    exact c1820 h u0_121 u9_110 hv
  have u13_25 : T {0, 4, 8} := by
    by_contra hv
    exact c17732 h a234 hv u10_74 n108
  have u14_137 : ¬ Q {0, 1, 4, 8} := by
    intro hv
    exact c4139 h hv u8_76 u12_111 u6_113
  have u15_173 : ¬ Q {0, 3, 4, 8} := by
    intro hv
    exact c9181 h hv u8_76 u12_111 u6_113
  have u16_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c370 h hv u14_137 u7_158 u15_173 n190 n192 u11_194
  exact c362 h u13_25 u14_137 u7_158 u15_173 u16_187 n190 n192 u11_194

end BorsukNine.FiniteObstruction

end OAI
