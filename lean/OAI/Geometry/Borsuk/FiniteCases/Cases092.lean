import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases091

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31443 (h : TenSystem T Q) :
    ¬ Q {0, 3, 5, 8} → ¬ Q {0, 1, 5, 8} → T {0, 5, 8} → ¬ Q {0, 5, 8, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n177 n141 a29 n200 n162 n198 n196
  have u0_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c430 h hv n141 n162 n177 n196 n198 n200
  exact c422 h a29 n141 n162 n177 u0_187 n196 n198 n200

private theorem c31444 (h : TenSystem T Q) :
    T {2, 4, 6} → ¬ T {2, 6, 7} → ¬ Q {1, 3, 5, 9} → T {5, 7, 8} → ¬ Q {1, 3, 6, 9} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a72 n80 n234 a114 n237 a230 n240 n210
  have u0_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv a114
  have u1_81 : T {2, 6, 8} := by
    by_contra hv
    exact c17134 h a230 u0_12 n80 hv
  have u2_76 : T {2, 5, 6} := by
    by_contra hv
    exact c17130 h a230 u0_12 hv n80
  have u3_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18405 h hv a72 u2_76 u1_81
  have u4_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3485 h hv a72 a114
  exact c728 h a230 u4_133 n210 n234 n237 u3_239 n240

private theorem c31445 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → T {4, 7, 9} → False := by
  classical
  intro a177 n72 n80 a109
  have u0_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c9645 h a177 hv a109
  exact c9710 h a177 u0_40 n72 n80

private theorem c31446 (h : TenSystem T Q) :
    T {0, 5, 8} → ¬ Q {1, 3, 5, 9} → ¬ Q {0, 5, 8, 9} → T {5, 7, 8} → T {4, 7, 9} → ¬ Q {0, 2, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a29 n234 n200 a114 a109 n162 n237 n198 n196 a230 n240 n210
  have u0_80 : ¬ T {2, 6, 7} := by
    intro hv
    exact c17075 h a230 a29 hv
  have u1_72 : ¬ T {2, 4, 6} := by
    intro hv
    exact c31444 h hv u0_80 n234 a114 n237 a230 n240 n210
  have u2_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c31445 h hv u1_72 u0_80 a109
  have u3_141 : Q {0, 1, 5, 8} := by
    by_contra hv
    exact c31443 h u2_177 hv a29 n200 n162 n198 n196
  have u4_67 : ¬ T {2, 3, 6} := by
    intro hv
    exact c4605 h u3_141 hv a109
  exact c4638 h u3_141 u4_67 u1_72 u0_80

theorem c31447 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {0, 2, 5, 8} → T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 5, 6, 7} → ¬ Q {0, 5, 6, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro n162 a103 n237 n198 n195 n286 n196 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  have u3_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u4_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c1807 h u0_121 a103 hv
  have u5_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u6_112 : ¬ T {5, 6, 8} := by
    intro hv
    exact c31441 h h0 hv n162 a103 n237 n198 n196 a230 n240 n210
  have u7_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1818 h u0_121 hv u6_112
  have u8_13 : T {0, 2, 7} := by
    by_contra hv
    exact c17066 h a230 hv u6_112
  have u9_114 : T {5, 7, 8} := by
    by_contra hv
    exact c31442 h h0 hv u6_112 a103 n195 n286 a230
  have u10_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u0_121 hv u9_114
  have u11_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1883 h u0_121 a103 u9_114 hv
  have u12_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv u9_114
  have u13_113 : T {5, 6, 9} := by
    by_contra hv
    exact c1910 h u0_121 u10_107 hv u4_118
  have u14_200 : ¬ Q {0, 5, 8, 9} := by
    intro hv
    exact c1728 h hv u11_116
  have u15_108 : ¬ T {4, 7, 8} := by
    intro hv
    exact c1817 h u0_121 hv u13_113
  have u16_234 : ¬ Q {1, 3, 5, 9} := by
    intro hv
    exact c17624 h hv u12_12 u15_108
  have u17_29 : ¬ T {0, 5, 8} := by
    intro hv
    exact c31446 h hv u16_234 u14_200 u9_114 u7_109 n162 n237 n198 n196 a230 n240 n210
  have u18_80 : T {2, 6, 7} := by
    by_contra hv
    exact c17074 h a230 u17_29 hv
  have u19_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3497 h hv u18_80 a103
  have u20_239 : Q {1, 3, 7, 9} := by
    by_contra hv
    exact c728 h a230 u19_133 n210 u16_234 n237 hv n240
  have u21_47 : T {1, 3, 7} := by
    by_contra hv
    exact c705 h u20_239 hv
  have u22_10 : T {0, 2, 4} := by
    by_contra hv
    exact c18322 h u20_239 hv u6_112
  have u23_288 : ¬ Q {2, 5, 6, 9} := by
    intro hv
    exact c25243 h hv u1_2 u5_44 u21_47
  have u24_197 : ¬ Q {0, 5, 6, 9} := by
    intro hv
    exact c12471 h hv u2_37 u5_44 u21_47
  have u25_253 : ¬ Q {1, 5, 6, 9} := by
    intro hv
    exact c20303 h hv u3_9 u22_10 u8_13
  exact c31376 h h0 u24_197 u13_113 u25_253 u23_288

theorem c31448 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → Q {1, 3, 4, 9} → T {1, 3, 9} → False := by
  classical
  intro a162 a230 a49
  have u0_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u1_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u2_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u3_59 : ¬ T {1, 6, 7} := by
    intro hv
    exact c7557 h a162 hv u0_90
  have u4_46 : ¬ T {1, 3, 6} := by
    intro hv
    exact c7565 h a162 u2_44 hv a49
  have u5_51 : ¬ T {1, 4, 6} := by
    intro hv
    exact c7573 h a162 u2_44 hv u1_54
  exact c7578 h a162 u4_46 u5_51 u3_59

theorem c31449 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {1, 6, 7} → ¬ T {1, 4, 6} → ¬ T {1, 3, 6} → ¬ T {4, 5, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {0, 6, 7, 8} → ¬ Q {0, 5, 6, 7} → ¬ Q {2, 6, 7, 8} → ¬ Q {2, 5, 7, 8} → ¬ Q {2, 5, 6, 7} → Q {1, 3, 4, 9} → False := by
  classical
  intro n59 n51 n46 n103 n198 n201 n195 n292 n289 n286 a230
  have u0_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u1_316 : ¬ Q {4, 5, 6, 7} := by
    intro hv
    exact c31221 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u3_322 : ¬ Q {4, 6, 7, 8} := by
    intro hv
    exact c31215 h h0 hv
  have u4_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u5_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u6_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u7_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u8_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u9_168 : ¬ Q {0, 2, 7, 9} := by
    intro hv
    exact c8386 h hv n46 n103
  have u10_235 : ¬ Q {1, 3, 6, 7} := by
    intro hv
    exact c686 h hv n46
  have u11_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1340 h a230 hv
  have u12_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u13_251 : ¬ Q {1, 5, 6, 7} := by
    intro hv
    exact c881 h hv n59
  have u14_257 : ¬ Q {1, 6, 7, 8} := by
    intro hv
    exact c883 h hv n59
  have u15_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6436 h hv n59 n103
  have u16_163 : ¬ Q {0, 2, 5, 9} := by
    intro hv
    exact c7718 h hv n46 n51 n59
  have u17_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c8568 h hv n46 n51 n59
  have u18_306 : ¬ Q {3, 5, 6, 7} := by
    intro hv
    exact c1660 h hv n195 u13_251 n286 u1_316 u7_326 u0_327
  have u19_111 : ¬ T {5, 6, 7} := by
    intro hv
    exact c31378 h h0 n286 hv u13_251 n195
  have u20_312 : ¬ Q {3, 6, 7, 8} := by
    intro hv
    exact c1750 h hv n201 u14_257 n292 u3_322 u7_326 u2_330
  have u21_110 : T {4, 8, 9} := by
    by_contra hv
    exact c1820 h u5_121 hv u19_111
  have u22_14 : T {0, 2, 8} := by
    by_contra hv
    exact c17068 h a230 hv u19_111
  have u23_117 : ¬ T {6, 7, 8} := by
    intro hv
    exact c1742 h hv n201 u14_257 n292 u20_312 u3_322 u7_326 u2_330
  have u24_161 : ¬ Q {0, 2, 5, 7} := by
    intro hv
    exact c7513 h hv u12_54 u11_90 u21_110
  have u25_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7933 h hv u12_54 u11_90 u21_110
  have u26_104 : T {4, 5, 9} := by
    by_contra hv
    exact c1808 h u5_121 hv u23_117
  have u27_11 : T {0, 2, 5} := by
    by_contra hv
    exact c17062 h a230 hv u23_117
  have u28_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c7242 h hv n59 u19_111 u23_117
  have u29_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c10035 h hv u12_54 u26_104 u21_110
  have u30_167 : ¬ Q {0, 2, 7, 8} := by
    intro hv
    exact c8351 h hv u12_54 u11_90 u26_104
  have u31_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1857 h u5_121 u26_104 hv u21_110
  have u32_270 : ¬ Q {2, 3, 6, 7} := by
    intro hv
    exact c22777 h hv u12_54 u26_104 u21_110
  have u33_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c6229 h hv u12_54 u26_104 u21_110
  have u34_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2449 h hv u11_90 u26_104 u21_110
  have u35_313 : ¬ Q {3, 6, 7, 9} := by
    intro hv
    exact c28715 h hv u4_1 u27_11 u22_14
  have u36_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17085 h a230 u27_11 hv u22_14
  have u37_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c26891 h hv u4_1 u27_11 u22_14
  have u38_95 : ¬ T {3, 6, 7} := by
    intro hv
    exact c1412 h hv u29_179 u10_235 u32_270 u37_300 u18_306 u20_312 u35_313
  have u39_157 : ¬ Q {0, 2, 4, 7} := by
    intro hv
    exact c188 h hv u34_125 u33_152 u24_161 u25_164 u30_167 u9_168
  have u40_114 : T {5, 7, 8} := by
    by_contra hv
    exact c1814 h u5_121 u31_107 hv
  have u41_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c172 h hv u36_12
  have u42_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c180 h hv u36_12
  have u43_158 : ¬ Q {0, 2, 4, 8} := by
    intro hv
    exact c7098 h hv n59 u38_95 u19_111
  have u44_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c2656 h hv u38_95 n103
  have u45_122 : ¬ Q {0, 1, 2, 4} := by
    intro hv
    exact c2034 h hv u38_95 u19_111 u23_117
  have u46_155 : ¬ Q {0, 2, 4, 5} := by
    intro hv
    exact c6654 h hv n59 u38_95 u23_117
  have u47_15 : ¬ T {0, 2, 9} := by
    intro hv
    exact c212 h hv u44_127 u15_154 u28_159 u16_163 u42_166 u9_168 u17_169
  have u48_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c31290 h u39_157 u43_158 u28_159 hv u41_156 u45_122 u46_155
  have u49_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c20448 h hv u48_10 u36_12 u47_15
  have u50_309 : ¬ Q {3, 5, 7, 8} := by
    intro hv
    exact c28156 h hv u48_10 u36_12 u47_15
  exact c1697 h u40_114 n198 u49_254 n289 u50_309 u8_319 u7_326 u6_329

theorem c31450 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {3, 5, 7, 8} → T {5, 7, 8} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → False := by
  classical
  intro n309 a114 n198 n289
  have u0_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u1_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u2_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u3_254 : ¬ Q {1, 5, 7, 8} := by
    intro hv
    exact c1701 h hv n198 n289 n309 u2_319 u1_326 u0_329
  exact c1697 h a114 n198 u3_254 n289 n309 u2_319 u1_326 u0_329

theorem c31451 (h : TenSystem T Q) :
    ¬ Q {0, 2, 5, 9} → ¬ Q {0, 1, 2, 9} → ¬ Q {0, 2, 4, 9} → ¬ Q {0, 2, 3, 9} → T {0, 2, 9} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  classical
  intro n163 n127 n159 n154 a15 n166 n168
  have u0_169 : ¬ Q {0, 2, 8, 9} := by
    intro hv
    exact c226 h hv n127 n154 n159 n163 n166 n168
  exact c212 h a15 n127 n154 n159 n163 n166 n168 u0_169

private theorem c31452 (h : TenSystem T Q) :
    ¬ T {0, 2, 4} → Q {1, 3, 5, 9} → ¬ Q {0, 2, 3, 9} → T {0, 2, 9} → Q {3, 5, 7, 8} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → Q {1, 3, 4, 9} → False := by
  classical
  intro n10 a234 n154 a15 a309 n166 n168 a230
  have u0_54 : T {1, 4, 9} := by
    by_contra hv
    exact c802 h a230 hv
  have u1_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u2_159 : ¬ Q {0, 2, 4, 9} := by
    intro hv
    exact c150 h hv n10
  have u3_61 : T {1, 6, 9} := by
    by_contra hv
    exact c28130 h a309 n10 hv
  have u4_43 : ¬ T {1, 2, 9} := by
    intro hv
    exact c28213 h a309 hv u0_54 u3_61
  have u5_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c633 h hv u4_43
  have u6_163 : Q {0, 2, 5, 9} := by
    by_contra hv
    exact c31451 h hv u5_127 u2_159 n154 a15 n166 n168
  have u7_117 : T {6, 7, 8} := by
    by_contra hv
    exact c17622 h a234 n10 hv
  exact c7683 h u6_163 u1_44 u7_117

theorem c31453 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 3, 5, 9} → ¬ Q {0, 2, 3, 9} → Q {1, 3, 4, 9} → T {0, 2, 9} → Q {3, 5, 7, 8} → ¬ Q {0, 2, 6, 9} → ¬ Q {0, 2, 7, 9} → False := by
  classical
  intro a234 n154 a230 a15 a309 n166 n168
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_10 : T {0, 2, 4} := by
    by_contra hv
    exact c31452 h hv a234 n154 a15 a309 n166 n168 a230
  exact c28153 h a309 u0_1 u1_10 a15

theorem c31454 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → T {1, 6, 7} → ¬ T {1, 4, 6} → ¬ Q {0, 2, 7, 9} → ¬ T {4, 5, 8} → ¬ Q {1, 3, 6, 9} → ¬ Q {0, 5, 7, 8} → ¬ Q {2, 5, 7, 8} → Q {1, 3, 4, 9} → ¬ Q {1, 3, 8, 9} → ¬ Q {1, 2, 3, 9} → False := by
  classical
  intro a114 a59 n51 n168 n103 n237 n198 n289 a230 n240 n210
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_326 : ¬ Q {5, 6, 7, 8} := by
    intro hv
    exact c31211 h h0 hv
  have u3_319 : ¬ Q {4, 5, 7, 8} := by
    intro hv
    exact c31218 h h0 hv
  have u4_44 : T {1, 3, 4} := by
    by_contra hv
    exact c660 h a230 hv
  have u5_107 : ¬ T {4, 6, 9} := by
    intro hv
    exact c1815 h u0_121 hv a114
  have u6_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c17065 h a230 hv a114
  have u7_166 : ¬ Q {0, 2, 6, 9} := by
    intro hv
    exact c8103 h hv u4_44 a114
  have u8_239 : ¬ Q {1, 3, 7, 9} := by
    intro hv
    exact c18326 h hv u6_12 n103
  have u9_309 : Q {3, 5, 7, 8} := by
    by_contra hv
    exact c31450 h h0 hv a114 n198 n289
  have u10_254 : Q {1, 5, 7, 8} := by
    by_contra hv
    exact c1705 h u9_309 n198 hv n289 u3_319 u2_326 u1_329
  have u11_15 : T {0, 2, 9} := by
    by_contra hv
    exact c28134 h u9_309 hv n51
  have u12_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28244 h u9_309 n51 hv u5_107
  have u13_56 : T {1, 5, 7} := by
    by_contra hv
    exact c838 h u10_254 hv
  have u14_62 : T {1, 7, 8} := by
    by_contra hv
    exact c926 h u10_254 hv
  have u15_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3485 h hv u12_72 a114
  have u16_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c6473 h hv u13_56 a59 u14_62
  have u17_234 : Q {1, 3, 5, 9} := by
    by_contra hv
    exact c728 h a230 u15_133 n210 hv n237 u8_239 n240
  exact c31453 h h0 u17_234 u16_154 a230 u11_15 u9_309 u7_166 n168

end BorsukNine.FiniteObstruction

end OAI
