import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases003
import OAI.Geometry.Borsuk.FiniteCases.Cases012
import OAI.Geometry.Borsuk.FiniteCases.Cases020
import OAI.Geometry.Borsuk.FiniteCases.Cases023
import OAI.Geometry.Borsuk.FiniteCases.Cases025
import OAI.Geometry.Borsuk.FiniteCases.Cases026
import OAI.Geometry.Borsuk.FiniteCases.Cases043
import OAI.Geometry.Borsuk.FiniteCases.Cases058
import OAI.Geometry.Borsuk.FiniteCases.Cases059
import OAI.Geometry.Borsuk.FiniteCases.Cases062
import OAI.Geometry.Borsuk.FiniteCases.Cases064
import OAI.Geometry.Borsuk.FiniteCases.Cases066
import OAI.Geometry.Borsuk.FiniteCases.Cases074
import OAI.Geometry.Borsuk.FiniteCases.Cases075
import OAI.Geometry.Borsuk.FiniteCases.Cases076

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31209 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 6, 8, 9} → False := by
  classical
  intro a328
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30803 h a328 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30811 h a328 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30819 h a328 u1_2 u2_9 hv
  exact c30826 h a328 u3_3 u4_10 u5_16

theorem c31210 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 6, 7, 9} → False := by
  classical
  intro a327
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30663 h a327 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30671 h a327 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30679 h a327 u1_2 u2_9 hv
  exact c30686 h a327 u3_3 u4_10 u5_16

theorem c31211 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {5, 6, 7, 8} → False := by
  classical
  intro a326
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_3 : ¬ T {0, 1, 4} := by
    intro hv
    exact c30523 h a326 u0_1 u1_2 hv
  have u4_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c30531 h a326 u0_1 u2_9 hv
  have u5_16 : ¬ T {0, 3, 4} := by
    intro hv
    exact c30539 h a326 u1_2 u2_9 hv
  exact c30546 h a326 u3_3 u4_10 u5_16

theorem c31212 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 7, 8, 9} → False := by
  classical
  intro a325
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c30383 h a325 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c30391 h a325 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c30399 h a325 u1_2 u2_9 hv
  exact c30406 h a325 u3_4 u4_11 u5_17

theorem c31213 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 6, 8, 9} → False := by
  classical
  intro a324
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c30243 h a324 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c30251 h a324 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c30259 h a324 u1_2 u2_9 hv
  exact c30266 h a324 u3_4 u4_11 u5_17

theorem c31214 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 6, 7, 9} → False := by
  classical
  intro a323
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c30103 h a323 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c30111 h a323 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c30119 h a323 u1_2 u2_9 hv
  exact c30126 h a323 u3_4 u4_11 u5_17

theorem c31215 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 6, 7, 8} → False := by
  classical
  intro a322
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c29963 h a322 u0_1 u1_2 hv
  have u4_11 : ¬ T {0, 2, 5} := by
    intro hv
    exact c29971 h a322 u0_1 u2_9 hv
  have u5_17 : ¬ T {0, 3, 5} := by
    intro hv
    exact c29979 h a322 u1_2 u2_9 hv
  exact c29986 h a322 u3_4 u4_11 u5_17

theorem c31216 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 8, 9} → False := by
  classical
  intro a321
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c29823 h a321 u0_1 u1_2 hv
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29831 h a321 u0_1 u2_9 hv
  have u5_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c29839 h a321 u1_2 u2_9 hv
  exact c29846 h a321 u3_5 u4_12 u5_18

theorem c31217 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 7, 9} → False := by
  classical
  intro a320
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c29683 h a320 u0_1 u1_2 hv
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29691 h a320 u0_1 u2_9 hv
  have u5_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c29699 h a320 u1_2 u2_9 hv
  exact c29706 h a320 u3_5 u4_12 u5_18

theorem c31218 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 7, 8} → False := by
  classical
  intro a319
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c29543 h a319 u0_1 u1_2 hv
  have u4_12 : ¬ T {0, 2, 6} := by
    intro hv
    exact c29551 h a319 u0_1 u2_9 hv
  have u5_18 : ¬ T {0, 3, 6} := by
    intro hv
    exact c29559 h a319 u1_2 u2_9 hv
  exact c29566 h a319 u3_5 u4_12 u5_18

theorem c31219 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 6, 9} → False := by
  classical
  intro a318
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c29403 h a318 u0_1 u1_2 hv
  have u4_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c29411 h a318 u0_1 u2_9 hv
  have u5_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c29419 h a318 u1_2 u2_9 hv
  exact c29426 h a318 u3_6 u4_13 u5_19

theorem c31220 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 6, 8} → False := by
  classical
  intro a317
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c29263 h a317 u0_1 u1_2 hv
  have u4_13 : ¬ T {0, 2, 7} := by
    intro hv
    exact c29271 h a317 u0_1 u2_9 hv
  have u5_19 : ¬ T {0, 3, 7} := by
    intro hv
    exact c29279 h a317 u1_2 u2_9 hv
  exact c29286 h a317 u3_6 u4_13 u5_19

theorem c31221 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {4, 5, 6, 7} → False := by
  classical
  intro a316
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u1_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u2_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  have u3_7 : ¬ T {0, 1, 8} := by
    intro hv
    exact c29123 h a316 u0_1 u1_2 hv
  have u4_14 : ¬ T {0, 2, 8} := by
    intro hv
    exact c29131 h a316 u0_1 u2_9 hv
  have u5_20 : ¬ T {0, 3, 8} := by
    intro hv
    exact c29139 h a316 u1_2 u2_9 hv
  exact c29146 h a316 u3_7 u4_14 u5_20

theorem c31226 (h : TenSystem T Q) :
    ¬ Q {2, 4, 6, 8} → ¬ Q {2, 4, 6, 9} → ¬ Q {0, 2, 4, 6} → T {2, 4, 6} →
      ¬ Q {2, 4, 5, 6} → ¬ Q {1, 2, 4, 6} → ¬ Q {2, 3, 4, 6} → False := by
  classical
  intro n281 n282 n156 a72 n276 n212 n262
  have u0_280 : Q {2, 4, 6, 7} := by
    by_contra hv
    exact c1067 h a72 n156 n212 n262 n276 hv n281 n282
  exact c1077 h u0_280 n156 n212 n262 n276 n281 n282

private theorem c31227 (h : TenSystem T Q) :
    T {3, 5, 7} → ¬ Q {2, 3, 4, 6} → T {1, 5, 7} → T {0, 5, 7} →
      ¬ Q {0, 2, 4, 6} → ¬ Q {1, 2, 4, 6} → T {2, 4, 6} → ¬ Q {2, 4, 5, 6} → False := by
  classical
  intro a92 n262 a56 a28 n156 n212 a72 n276
  have u0_281 : ¬ Q {2, 4, 6, 8} := by
    intro hv
    exact c24319 h hv a28 a56 a92
  have u1_282 : ¬ Q {2, 4, 6, 9} := by
    intro hv
    exact c24459 h hv a28 a56 a92
  exact c31226 h u0_281 u1_282 n156 a72 n276 n212 n262

theorem c31228 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → Q {3, 7, 8, 9} → T {0, 1, 4} → False := by
  classical
  intro a314 a315 a3
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  have u1_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  have u2_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  have u3_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  have u4_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u5_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u6_101 : ¬ T {4, 5, 6} := by
    intro hv
    exact c28963 h a315 u1_1 hv
  have u7_76 : ¬ T {2, 5, 6} := by
    intro hv
    exact c28965 h a315 a3 hv
  have u8_55 : T {1, 5, 6} := by
    by_contra hv
    exact c29100 h a315 hv u7_76 u6_101
  have u9_10 : ¬ T {0, 2, 4} := by
    intro hv
    exact c28971 h a315 hv u8_55
  have u10_156 : ¬ Q {0, 2, 4, 6} := by
    intro hv
    exact c144 h hv u9_10
  have u11_27 : T {0, 5, 6} := by
    by_contra hv
    exact c29098 h a315 hv u7_76 u6_101
  have u12_38 : ¬ T {1, 2, 4} := by
    intro hv
    exact c28981 h a315 u11_27 hv
  have u13_212 : ¬ Q {1, 2, 4, 6} := by
    intro hv
    exact c564 h hv u12_38
  have u14_5 : ¬ T {0, 1, 6} := by
    intro hv
    exact c28985 h a315 u1_1 a3 hv
  have u15_71 : T {2, 4, 5} := by
    by_contra hv
    exact c28968 h a315 u14_5 hv
  have u16_130 : ¬ Q {0, 1, 3, 6} := by
    intro hv
    exact c65 h hv u14_5
  have u17_4 : ¬ T {0, 1, 5} := by
    intro hv
    exact c28983 h a315 u1_1 a3 hv
  have u18_72 : T {2, 4, 6} := by
    by_contra hv
    exact c28966 h a315 u17_4 hv
  have u19_129 : ¬ Q {0, 1, 3, 5} := by
    intro hv
    exact c50 h hv u17_4
  have u20_120 : T {7, 8, 9} := by
    by_contra hv
    exact c1794 h a315 hv
  have u21_276 : ¬ Q {2, 4, 5, 6} := by
    intro hv
    exact c23503 h hv u0_2 u20_120
  have u22_119 : T {6, 8, 9} := by
    by_contra hv
    exact c1779 h a314 hv
  have u23_6 : ¬ T {0, 1, 7} := by
    intro hv
    exact c28845 h a314 u1_1 a3 hv
  have u24_73 : T {2, 4, 7} := by
    by_contra hv
    exact c28826 h a314 u17_4 hv
  have u25_28 : T {0, 5, 7} := by
    by_contra hv
    exact c28840 h a314 hv u12_38
  have u26_56 : T {1, 5, 7} := by
    by_contra hv
    exact c28830 h a314 u9_10 hv
  have u27_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c1941 h u2_121 hv u22_119 u20_120
  have u28_131 : ¬ Q {0, 1, 3, 7} := by
    intro hv
    exact c3203 h hv u15_71 u22_119
  have u29_262 : ¬ Q {2, 3, 4, 6} := by
    intro hv
    exact c21544 h hv u23_6 u27_116
  have u30_132 : ¬ Q {0, 1, 3, 8} := by
    intro hv
    exact c3363 h hv u15_71 u18_72 u24_73
  have u31_133 : ¬ Q {0, 1, 3, 9} := by
    intro hv
    exact c3503 h hv u15_71 u18_72 u24_73
  have u32_128 : Q {0, 1, 3, 4} := by
    by_contra hv
    exact c19 h u2_121 hv u19_129 u16_130 u28_131 u30_132 u31_133
  have u33_16 : T {0, 3, 4} := by
    by_contra hv
    exact c228 h u32_128 hv
  have u34_294 : ¬ Q {2, 6, 8, 9} := by
    intro hv
    exact c26031 h hv u33_16 u26_56
  have u35_92 : ¬ T {3, 5, 7} := by
    intro hv
    exact c31227 h hv u29_262 u26_56 u25_28 u10_156 u13_212 u18_72 u21_276
  have u36_259 : ¬ Q {1, 6, 8, 9} := by
    intro hv
    exact c21124 h hv u9_10 u35_92
  have u37_203 : ¬ Q {0, 6, 8, 9} := by
    intro hv
    exact c13284 h hv u12_38 u35_92
  exact c1780 h a314 u37_203 u36_259 u34_294 u5_324 u4_328 u3_330

end BorsukNine.FiniteObstruction

end OAI
