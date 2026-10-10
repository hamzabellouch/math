import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y11YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV0_arg_eq :
    barrierCase2Y11YV0LogArg = barrierComplex (2478470229 / 781250000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV0LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV0_arg_regular :
    (barrierCase2Y11YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV0LogArg).re := by
  rw [barrierCase2Y11YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y11YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (6142814676039312441 / 4882812500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y11YV0LogArg (3) (0) (6142814676039312441 / 4882812500000000000) (2478470229 / 781250000) (0 / 1)
  have hratio : ((0 / 1) / (2478470229 / 781250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (6142814676039312441 / 4882812500000000000) (0 / 1) <
      (-175475134886 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-175475134886 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y11YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (6142814676039312441 / 4882812500000000000) (0 / 1) : ℚ) : ℝ) <
      (-175475134886 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV1_arg_eq :
    barrierCase2Y11YV1LogArg = barrierComplex (7344785687 / 1953125000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV1LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV1_arg_regular :
    (barrierCase2Y11YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV1LogArg).re := by
  rw [barrierCase2Y11YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y11YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (53945876787960061969 / 30517578125000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y11YV1LogArg (3) (0) (53945876787960061969 / 30517578125000000000) (7344785687 / 1953125000) (0 / 1)
  have hratio : ((0 / 1) / (7344785687 / 1953125000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (53945876787960061969 / 30517578125000000000) (0 / 1) <
      (-58964933170 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-58964933170 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y11YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (53945876787960061969 / 30517578125000000000) (0 / 1) : ℚ) : ℝ) <
      (-58964933170 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV2_arg_eq :
    barrierCase2Y11YV2LogArg = barrierComplex (693077481 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV2LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV2_arg_regular :
    (barrierCase2Y11YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV2LogArg).re := by
  rw [barrierCase2Y11YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y11YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-7) (0) (480356394669305361 / 476837158203125000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y11YV2LogArg (-7) (0) (480356394669305361 / 476837158203125000) (693077481 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (693077481 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-7) (0) (480356394669305361 / 476837158203125000) (0 / 1) <
      (61658155630 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (61658155630 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y11YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-7) (0) (480356394669305361 / 476837158203125000) (0 / 1) : ℚ) : ℝ) <
      (61658155630 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV3_arg_eq :
    barrierCase2Y11YV3LogArg = barrierComplex (1034065649 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV3LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV3_arg_regular :
    (barrierCase2Y11YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV3LogArg).re := by
  rw [barrierCase2Y11YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y11YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-8) (0) (1069291766441791201 / 610351562500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y11YV3LogArg (-8) (0) (1069291766441791201 / 610351562500000000) (1034065649 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (1034065649 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-8) (0) (1069291766441791201 / 610351562500000000) (0 / 1) <
      (-122932603076 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-122932603076 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y11YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-8) (0) (1069291766441791201 / 610351562500000000) (0 / 1) : ℚ) : ℝ) <
      (-122932603076 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV4_arg_eq :
    barrierCase2Y11YV4LogArg = barrierComplex (6511911833 / 78125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV4LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV4_arg_regular :
    (barrierCase2Y11YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV4LogArg).re := by
  rw [barrierCase2Y11YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y11YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-8) (0) (42404995720765419889 / 23841857910156250000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y11YV4LogArg (-8) (0) (42404995720765419889 / 23841857910156250000) (6511911833 / 78125000000) (0 / 1)
  have hratio : ((0 / 1) / (6511911833 / 78125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-8) (0) (42404995720765419889 / 23841857910156250000) (0 / 1) <
      (288673676966 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (288673676966 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y11YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-8) (0) (42404995720765419889 / 23841857910156250000) (0 / 1) : ℚ) : ℝ) <
      (288673676966 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV5_arg_eq :
    barrierCase2Y11YV5LogArg = barrierComplex (979 / 2500) (-46691588931 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV5LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV5_arg_regular :
    (barrierCase2Y11YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV5LogArg).re := by
  rw [barrierCase2Y11YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y11YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (2329860883151481722761 / 1953125000000000000000) (12237500000 / 46691588931) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y11YV5LogArg (1) (-2) (2329860883151481722761 / 1953125000000000000000) (46691588931 / 15625000000) (979 / 1250)
  have hratio : ((979 / 1250) / (46691588931 / 15625000000) : ℚ) = (12237500000 / 46691588931) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (2329860883151481722761 / 1953125000000000000000) (12237500000 / 46691588931) <
      (-311905072575 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-311905072575 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y11YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (2329860883151481722761 / 1953125000000000000000) (12237500000 / 46691588931) : ℚ) : ℝ) <
      (-311905072575 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y11YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV7_arg_eq :
    barrierCase2Y11YV7LogArg = barrierComplex (19 / 100) (-10774982061 / 6250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV7LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV7_arg_regular :
    (barrierCase2Y11YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV7LogArg).re := by
  rw [barrierCase2Y11YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y11YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (117510394664871807721 / 78125000000000000000) (62500000 / 567104319) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y11YV7LogArg (1) (-2) (117510394664871807721 / 78125000000000000000) (10774982061 / 3125000000) (19 / 50)
  have hratio : ((19 / 50) / (10774982061 / 3125000000) : ℚ) = (62500000 / 567104319) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (117510394664871807721 / 78125000000000000000) (62500000 / 567104319) <
      (-134238812104 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-134238812104 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y11YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (117510394664871807721 / 78125000000000000000) (62500000 / 567104319) : ℚ) : ℝ) <
      (-134238812104 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV9_arg_eq :
    barrierCase2Y11YV9LogArg = barrierComplex (3519 / 40000) (-228669063739 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV9LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV9_arg_regular :
    (barrierCase2Y11YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV9LogArg).re := by
  rw [barrierCase2Y11YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y11YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (52410471971036469660121 / 31250000000000000000000) (10996875000 / 228669063739) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y11YV9LogArg (1) (-2) (52410471971036469660121 / 31250000000000000000000) (228669063739 / 62500000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (228669063739 / 62500000000) : ℚ) = (10996875000 / 228669063739) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (52410471971036469660121 / 31250000000000000000000) (10996875000 / 228669063739) <
      (110948364935 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (110948364935 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y11YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (52410471971036469660121 / 31250000000000000000000) (10996875000 / 228669063739) : ℚ) : ℝ) <
      (110948364935 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y11YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y11 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y11YV11_arg_eq :
    barrierCase2Y11YV11LogArg = barrierComplex (496 / 15625) (-147258088167 / 78125000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y11YV11LogArg, Case2PointData.Y11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y11YV11_arg_regular :
    (barrierCase2Y11YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y11YV11LogArg).re := by
  rw [barrierCase2Y11YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y11YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y11YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y11YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (21691094930599945419889 / 12207031250000000000000) (2480000000 / 147258088167) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y11YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y11YV11LogArg (1) (-2) (21691094930599945419889 / 12207031250000000000000) (147258088167 / 39062500000) (992 / 15625)
  have hratio : ((992 / 15625) / (147258088167 / 39062500000) : ℚ) = (2480000000 / 147258088167) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y11YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y11YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (21691094930599945419889 / 12207031250000000000000) (2480000000 / 147258088167) <
      (-175242664064 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y11YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-175242664064 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y11YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y11YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (21691094930599945419889 / 12207031250000000000000) (2480000000 / 147258088167) : ℚ) : ℝ) <
      (-175242664064 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y11_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y11 : ℝ))).sum <
      (-1027917206152 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y11 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y11 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y11YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y11YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y11YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y11YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y11YV0_log_upper,
    barrierCase2Y11YV1_log_upper,
    barrierCase2Y11YV2_log_upper,
    barrierCase2Y11YV3_log_upper,
    barrierCase2Y11YV4_log_upper,
    barrierCase2Y11YV5_log_upper,
    barrierCase2Y11YV7_log_upper,
    barrierCase2Y11YV9_log_upper,
    barrierCase2Y11YV11_log_upper]

private theorem barrierCase2Y11_approx_upper :
    barrierCase2YApproxRat Y11 (-1) (-5) (1197220229 / 625000000) (52779771 / 39062500) + (-1027917206152 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y11_lt : barrierCase2Y (Y11 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y11 : ℝ)| ≤ 1 := by norm_num [Y11]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y11 hx
    (-1) (-5) (1197220229 / 625000000) (52779771 / 39062500)
    Y11_normalizations.1 Y11_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y11 (-1) (-5) (1197220229 / 625000000) (52779771 / 39062500) : ℚ) : ℝ) +
      (-1027917206152 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y11_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y11_YV_tail_upper]

end InternalCatalan

end

end OAI
