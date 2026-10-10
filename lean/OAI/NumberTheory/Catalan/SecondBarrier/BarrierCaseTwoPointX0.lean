import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogApprox
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX0Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoTailSums

namespace OAI

noncomputable section

namespace InternalCatalan

section
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

private theorem barrier_T_9 :
    Chebyshev.T ℚ 9 = 2 * X * Chebyshev.T ℚ 8 - Chebyshev.T ℚ 7 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 7

private theorem barrier_T_10 :
    Chebyshev.T ℚ 10 = 2 * X * Chebyshev.T ℚ 9 - Chebyshev.T ℚ 8 := by
  simpa only [Int.reduceAdd] using Chebyshev.T_add_two ℚ 8

def barrierCase2TPExplicit (x : ℚ) : ℚ :=
  (1191279397 / 4000000000 : ℚ) +
    (29086173 / 50000000 : ℚ) * x ^ 1 +
    (-49273657 / 50000000 : ℚ) * x ^ 2 +
    (-10371061 / 25000000 : ℚ) * x ^ 3 +
    (51185159 / 50000000 : ℚ) * x ^ 4 +
    (4435791 / 7812500 : ℚ) * x ^ 5 +
    (-1619803 / 1562500 : ℚ) * x ^ 6 +
    (-1319413 / 2734375 : ℚ) * x ^ 7 +
    (4083239 / 6250000 : ℚ) * x ^ 8 +
    (671564 / 3515625 : ℚ) * x ^ 9 +
    (-346453 / 1953125 : ℚ) * x ^ 10

theorem barrierCase2TP_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierP2Finite x = barrierCase2TPExplicit x := by
  norm_num [barrierFiniteTRat, barrierP2Finite, barrierCase2TPExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8, barrier_T_9, barrier_T_10]
  ring

def barrierCase2TVExplicit (x : ℚ) : ℚ :=
  (-277505287 / 2000000000 : ℚ) +
    (-9885373 / 100000000 : ℚ) * x ^ 1 +
    (51881119 / 100000000 : ℚ) * x ^ 2 +
    (-61236133 / 75000000 : ℚ) * x ^ 3 +
    (-16771643 / 50000000 : ℚ) * x ^ 4 +
    (57179319 / 31250000 : ℚ) * x ^ 5 +
    (-3124523 / 6250000 : ℚ) * x ^ 6 +
    (-1507689 / 781250 : ℚ) * x ^ 7 +
    (1759027 / 1562500 : ℚ) * x ^ 8 +
    (60938 / 78125 : ℚ) * x ^ 9 +
    (-1162454 / 1953125 : ℚ) * x ^ 10

theorem barrierCase2TV_eq_explicit (x : ℚ) :
    barrierFiniteTRat barrierV2Finite x = barrierCase2TVExplicit x := by
  norm_num [barrierFiniteTRat, barrierV2Finite, barrierCase2TVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8, barrier_T_9, barrier_T_10]
  ring

def barrierCase2SVExplicit (x : ℚ) : ℚ :=
  (-11955079 / 50000000 : ℚ) * x ^ 1 +
    (1322027 / 12500000 : ℚ) * x ^ 2 +
    (-288511 / 30000000 : ℚ) * x ^ 3 +
    (-11558199 / 400000000 : ℚ) * x ^ 4 +
    (6485289 / 500000000 : ℚ) * x ^ 5 +
    (485607 / 200000000 : ℚ) * x ^ 6 +
    (-17073 / 6250000 : ℚ) * x ^ 7 +
    (-565881 / 200000000 : ℚ) * x ^ 8 +
    (30469 / 10000000 : ℚ) * x ^ 9 +
    (-581227 / 500000000 : ℚ) * x ^ 10

theorem barrierCase2SV_eq_explicit (x : ℚ) :
    barrierFiniteSRat barrierV2Finite x = barrierCase2SVExplicit x := by
  norm_num [barrierFiniteSRat, barrierV2Finite, barrierCase2SVExplicit,
    Finset.sum_range_succ, Chebyshev.T_two, barrier_T_3, barrier_T_4,
    barrier_T_5, barrier_T_6, barrier_T_7, barrier_T_8, barrier_T_9, barrier_T_10]
  ring

end

def barrierCase2X0XV0LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X0XV0_arg_eq :
    barrierCase2X0XV0LogArg = barrierComplex (724722713 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV0LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV0_arg_regular :
    (barrierCase2X0XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV0LogArg).re := by
  rw [barrierCase2X0XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X0XV0LogArg (-5) (0) (525223010738080369 / 305175781250000000) (724722713 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (724722713 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1) <
      (-222121337235 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-222121337235 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1) : ℚ) : ℝ) <
      (-222121337235 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV1LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X0XV1_arg_eq :
    barrierCase2X0XV1LogArg = barrierComplex (611668139 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV1LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV1_arg_regular :
    (barrierCase2X0XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV1LogArg).re := by
  rw [barrierCase2X0XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X0XV1LogArg (-8) (0) (374137912267723321 / 238418579101562500) (611668139 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (611668139 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1) <
      (-113396759439 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-113396759439 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1) : ℚ) : ℝ) <
      (-113396759439 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV2LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X0XV2_arg_eq :
    barrierCase2X0XV2LogArg = barrierComplex (57653050157 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV2LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV2_arg_regular :
    (barrierCase2X0XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV2LogArg).re := by
  rw [barrierCase2X0XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X0XV2LogArg (1) (0) (3323874192405557724649 / 1953125000000000000000) (57653050157 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (57653050157 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1) <
      (15588622581 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (15588622581 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (15588622581 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV3LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X0XV3_arg_eq :
    barrierCase2X0XV3LogArg = barrierComplex (95605268453 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV3LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV3_arg_regular :
    (barrierCase2X0XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV3LogArg).re := by
  rw [barrierCase2X0XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X0XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X0XV3LogArg (1) (0) (9140367355970197013209 / 5000000000000000000000) (95605268453 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (95605268453 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1) <
      (-31973576393 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-31973576393 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X0XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (9140367355970197013209 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-31973576393 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV4LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X0XV4_arg_eq :
    barrierCase2X0XV4LogArg = barrierComplex (607734106301 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV4LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV4_arg_regular :
    (barrierCase2X0XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV4LogArg).re := by
  rw [barrierCase2X0XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X0XV4LogArg (1) (0) (369340743961475167902601 / 195312500000000000000000) (607734106301 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (607734106301 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1) <
      (77276195268 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (77276195268 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (369340743961475167902601 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (77276195268 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV5LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X0XV5_arg_eq :
    barrierCase2X0XV5LogArg = barrierComplex (1 / 1) (93610814193 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV5LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV5_arg_regular :
    (barrierCase2X0XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV5LogArg).re := by
  rw [barrierCase2X0XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X0XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X0XV5LogArg (0) (1) (24387984533876370241249 / 15625000000000000000000) (218610814193 / 125000000000) (-31389185807 / 125000000000)
  have hratio : ((-31389185807 / 125000000000) / (218610814193 / 125000000000) : ℚ) = (-31389185807 / 218610814193) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193) <
      (-93251437795 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-93251437795 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X0XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (1) (24387984533876370241249 / 15625000000000000000000) (-31389185807 / 218610814193) : ℚ) : ℝ) <
      (-93251437795 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV7LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X0XV7_arg_eq :
    barrierCase2X0XV7LogArg = barrierComplex (1 / 1) (21602495583 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV7LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV7_arg_regular :
    (barrierCase2X0XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV7LogArg).re := by
  rw [barrierCase2X0XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X0XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X0XV7LogArg (0) (1) (1091667815413534509889 / 625000000000000000000) (46602495583 / 25000000000) (-3397504417 / 25000000000)
  have hratio : ((-3397504417 / 25000000000) / (46602495583 / 25000000000) : ℚ) = (-3397504417 / 46602495583) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583) <
      (-151264226370 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-151264226370 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X0XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583) : ℚ) : ℝ) <
      (-151264226370 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV9LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X0XV9_arg_eq :
    barrierCase2X0XV9LogArg = barrierComplex (1 / 1) (458452961817 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV9LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV9_arg_regular :
    (barrierCase2X0XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV9LogArg).re := by
  rw [barrierCase2X0XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X0XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X0XV9LogArg (0) (1) (460179118198779659941489 / 250000000000000000000000) (958452961817 / 500000000000) (-41547038183 / 500000000000)
  have hratio : ((-41547038183 / 500000000000) / (958452961817 / 500000000000) : ℚ) = (-41547038183 / 958452961817) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817) <
      (33988820931 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (33988820931 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X0XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817) : ℚ) : ℝ) <
      (33988820931 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XV11LogArg : ℂ :=
  1 - ((Case2PointData.X0 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X0XV11_arg_eq :
    barrierCase2X0XV11LogArg = barrierComplex (1 / 1) (295234106301 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XV11LogArg, Case2PointData.X0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XV11_arg_regular :
    (barrierCase2X0XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XV11LogArg).re := by
  rw [barrierCase2X0XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X0XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X0XV11LogArg (0) (1) (184819427523350167902601 / 97656250000000000000000) (607734106301 / 312500000000) (-17265893699 / 312500000000)
  have hratio : ((-17265893699 / 312500000000) / (607734106301 / 312500000000) : ℚ) = (-17265893699 / 607734106301) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301) <
      (-78916320257 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-78916320257 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X0XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301) : ℚ) : ℝ) <
      (-78916320257 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X0_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X0 : ℝ))).sum <
      (-1479231423652 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X0 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X0 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X0XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X0XP0_log_upper,
    barrierCase2X0XP1_log_upper,
    barrierCase2X0XP2_log_upper,
    barrierCase2X0XP4_log_upper,
    barrierCase2X0XP6_log_upper,
    barrierCase2X0XP8_log_upper]

private theorem barrierCase2X0_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X0 : ℝ))).sum <
      (-853513182200 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X0 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X0 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X0XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X0XV0_log_upper,
    barrierCase2X0XV1_log_upper,
    barrierCase2X0XV2_log_upper,
    barrierCase2X0XV3_log_upper,
    barrierCase2X0XV4_log_upper,
    barrierCase2X0XV5_log_upper,
    barrierCase2X0XV7_log_upper,
    barrierCase2X0XV9_log_upper,
    barrierCase2X0XV11_log_upper]

private theorem barrierCase2X0_approx_upper :
    barrierCase2XApproxRat X0 (-1) (0) (0) (2400277287 / 1250000000) (4900277287 / 2500000000) (12011331054488080369 / 6250000000000000000) + (-1479231423652 / 1000000000000) + (-853513182200 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X0_lt : barrierCase2X (X0 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X0 : ℝ)| ≤ 1 := by norm_num [X0]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X0 hx
    (-1) (0) (0) (2400277287 / 1250000000) (4900277287 / 2500000000) (12011331054488080369 / 6250000000000000000)
    X0_normalizations.1 X0_normalizations.2.1 X0_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X0 (-1) (0) (0) (2400277287 / 1250000000) (4900277287 / 2500000000) (12011331054488080369 / 6250000000000000000) : ℚ) : ℝ) +
      (-1479231423652 / 1000000000000) + (-853513182200 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X0_XP_tail_upper, barrierCase2X0_XV_tail_upper]

end InternalCatalan

end

end OAI
