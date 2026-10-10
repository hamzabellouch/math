import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneBracketHeight

namespace OAI


noncomputable section
namespace InternalCatalan
open Polynomial

private theorem barrier_T_3 :
    Chebyshev.T ℚ 3 = 2 * X * Chebyshev.T ℚ 2 - Chebyshev.T ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 1

private theorem barrier_T_4 :
    Chebyshev.T ℚ 4 = 2 * X * Chebyshev.T ℚ 3 - Chebyshev.T ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 2

private theorem barrier_T_5 :
    Chebyshev.T ℚ 5 = 2 * X * Chebyshev.T ℚ 4 - Chebyshev.T ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 3

private theorem barrier_T_6 :
    Chebyshev.T ℚ 6 = 2 * X * Chebyshev.T ℚ 5 - Chebyshev.T ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 4

private theorem barrier_T_7 :
    Chebyshev.T ℚ 7 = 2 * X * Chebyshev.T ℚ 6 - Chebyshev.T ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 5

private theorem barrier_T_8 :
    Chebyshev.T ℚ 8 = 2 * X * Chebyshev.T ℚ 7 - Chebyshev.T ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 6

def barrierCase1TPExplicit (x : ℚ) : ℚ :=
  (1120821349 / 2400000000 : ℚ) +
    (2202187 / 5000000 : ℚ) * x ^ 1 +
    (-31132013 / 50000000 : ℚ) * x ^ 2 +
    (-50767033 / 75000000 : ℚ) * x ^ 3 +
    (-203194679 / 50000000 : ℚ) * x ^ 4 +
    (986599 / 3906250 : ℚ) * x ^ 5 +
    (5902457 / 750000 : ℚ) * x ^ 6 +
    (285123 / 5468750 : ℚ) * x ^ 7 +
    (-24939103 / 6250000 : ℚ) * x ^ 8

theorem barrierCase1TP_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierP1Finite x = barrierCase1TPExplicit x := by
  norm_num [barrierFiniteTRat, barrierP1Finite, barrierCase1TPExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8]
  ring

def barrierCase1TVExplicit (x : ℚ) : ℚ :=
  (-1005408749 / 2400000000 : ℚ) +
    (-41042587 / 25000000 : ℚ) * x ^ 1 +
    (28402743 / 10000000 : ℚ) * x ^ 2 +
    (16189271 / 7500000 : ℚ) * x ^ 3 +
    (-336320967 / 50000000 : ℚ) * x ^ 4 +
    (-34182773 / 15625000 : ℚ) * x ^ 5 +
    (67938223 / 9375000 : ℚ) * x ^ 6 +
    (9819141 / 10937500 : ℚ) * x ^ 7 +
    (-16992389 / 6250000 : ℚ) * x ^ 8

theorem barrierCase1TV_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierV1Finite x = barrierCase1TVExplicit x := by
  norm_num [barrierFiniteTRat, barrierV1Finite, barrierCase1TVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8]
  ring

def barrierCase1SVExplicit (x : ℚ) : ℚ :=
  (-3596521 / 4000000 : ℚ) * x ^ 1 +
    (1321857 / 5000000 : ℚ) * x ^ 2 +
    (45168341 / 300000000 : ℚ) * x ^ 3 +
    (-30708629 / 400000000 : ℚ) * x ^ 4 +
    (-19269841 / 500000000 : ℚ) * x ^ 5 +
    (530033 / 9375000 : ℚ) * x ^ 6 +
    (9819141 / 700000000 : ℚ) * x ^ 7 +
    (-16992389 / 800000000 : ℚ) * x ^ 8

theorem barrierCase1SV_eq_explicit (x : ℚ) :
    barrierFiniteSRat barrierV1Finite x = barrierCase1SVExplicit x := by
  norm_num [barrierFiniteSRat, barrierV1Finite, barrierCase1SVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8]
  ring

end InternalCatalan




namespace InternalCatalan

def barrierCase1XApproxRat (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ) : ℚ :=
  (19 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 -
    (41 / 48 : ℚ) * barrierScaledLogRat m2 y2 + barrierCase1XRat x

def barrierCase1YApproxRat (x : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ) : ℚ :=
  (7 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 + barrierCase1YRat x

theorem barrierCase1X_approx_error (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization |(x : ℝ)| m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1)
    (h2 : Case1PointData.FixedLogNormalization (1 + (x : ℝ) ^ 2) m2 y2) :
    |barrierCase1X (x : ℝ) -
      ((barrierCase1XApproxRat x m0 m1 m2 y0 y1 y2 : ℚ) : ℝ)| <
      (2 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  have he2 := abs_lt.mp (barrier_fixed_log_abs_error h2)
  rw [barrierCase1X_eval_rat]
  unfold barrierCase1XApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2, he2.1, he2.2]

theorem barrierCase1Y_approx_error (x : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization (x : ℝ) m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1) :
    |barrierCase1Y (x : ℝ) -
      ((barrierCase1YApproxRat x m0 m1 y0 y1 : ℚ) : ℝ)| <
      (1 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  rw [barrierCase1Y_eval_rat]
  unfold barrierCase1YApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2]





open Case1PointData

private theorem barrierCase1X0_approx_upper :
    barrierCase1XApproxRat X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X0, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X0_lt : barrierCase1X (X0 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000)
    X0_normalizations.1 X0_normalizations.2.1 X0_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X0 (-1) (0) (0) (1983459957 / 1000000000) (3983459957 / 2000000000) (7934113401022441849 / 4000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X0_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X1_approx_upper :
    barrierCase1XApproxRat X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X1, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X1_lt : barrierCase1X (X1 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000)
    X1_normalizations.1 X1_normalizations.2.1 X1_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X1 (-3) (0) (0) (2259572153 / 1250000000) (12259572153 / 10000000000) (105105666314613055409 / 100000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X1_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X2_approx_upper :
    barrierCase1XApproxRat X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X2, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X2_lt : barrierCase1X (X2 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000)
    X2_normalizations.1 X2_normalizations.2.1 X2_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X2 (-2) (-1) (0) (1271904013 / 1250000000) (3728095987 / 2500000000) (26617739818285504169 / 25000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X2_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X3_approx_upper :
    barrierCase1XApproxRat X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X3, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X3_lt : barrierCase1X (X3 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000)
    X3_normalizations.1 X3_normalizations.2.1 X3_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X3 (-2) (-1) (0) (4437270259 / 2500000000) (5562729741 / 5000000000) (119689367351405927081 / 100000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X3_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X4_approx_upper :
    barrierCase1XApproxRat X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X4, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X4_lt : barrierCase1X (X4 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000)
    X4_normalizations.1 X4_normalizations.2.1 X4_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X4 (-1) (-2) (0) (634829897 / 500000000) (365170103 / 250000000) (1403008998125030609 / 1000000000000000000) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X4_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X5_approx_upper :
    barrierCase1XApproxRat X5 (0) (1) (1) (1) (1) (1) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X5, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X5_lt : barrierCase1X (X5 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X5 (0) (1) (1) (1) (1) (1)
    X5_normalizations.1 X5_normalizations.2.1 X5_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X5 (0) (1) (1) (1) (1) (1) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X5_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X6_approx_upper :
    barrierCase1XApproxRat X6 (-1) (0) (0) (1) (3 / 2) (5 / 4) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X6, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X6_lt : barrierCase1X (X6 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X6 (-1) (0) (0) (1) (3 / 2) (5 / 4)
    X6_normalizations.1 X6_normalizations.2.1 X6_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X6 (-1) (0) (0) (1) (3 / 2) (5 / 4) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X6_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1X7_approx_upper :
    barrierCase1XApproxRat X7 (-1) (-1) (0) (1) (1) (5 / 4) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase1XApproxRat barrierCase1XRat
  rw [barrierCase1TP_eq_explicit, barrierCase1SV_eq_explicit]
  norm_num [X7, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1X7_lt : barrierCase1X (X7 : ℝ) < (-13244 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1X_approx_error X7 (-1) (-1) (0) (1) (1) (5 / 4)
    X7_normalizations.1 X7_normalizations.2.1 X7_normalizations.2.2)
  have ha : ((barrierCase1XApproxRat X7 (-1) (-1) (0) (1) (1) (5 / 4) : ℚ) : ℝ) <
      (-13244 / 10000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1X7_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y0_approx_upper :
    barrierCase1YApproxRat Y0 (-5) (-1)
      (266334893 / 156250000) (4733665107 / 2500000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y0, barrierCase1TVExplicit, barrierScaledLogRat,
    barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y0_lt : barrierCase1Y (Y0 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y0 (-5) (-1)
    (266334893 / 156250000) (4733665107 / 2500000000)
    Y0_normalizations.1 Y0_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y0 (-5) (-1)
      (266334893 / 156250000) (4733665107 / 2500000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y0_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan




namespace InternalCatalan
open Case1PointData

private theorem barrierCase1Y1_approx_upper :
    barrierCase1YApproxRat Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase1YApproxRat barrierCase1YRat
  rw [barrierCase1TV_eq_explicit]
  norm_num [Y1, barrierCase1TPExplicit, barrierCase1TVExplicit,
    barrierCase1SVExplicit, barrierScaledLogRat, barrierLogHRat, Finset.sum_range_succ]

theorem barrierCase1Y1_lt : barrierCase1Y (Y1 : ℝ) < (-14280 / 10000 : ℝ) := by
  have he := abs_lt.mp (barrierCase1Y_approx_error Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000)
    Y1_normalizations.1 Y1_normalizations.2)
  have ha : ((barrierCase1YApproxRat Y1 (-2) (-1) (100169573 / 100000000) (299830427 / 200000000) : ℚ) : ℝ) <
      (-14280 / 10000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase1Y1_approx_upper using 1
    norm_num
  linarith [he.2]

end InternalCatalan

end

end OAI
