import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y15YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV0_arg_eq :
    barrierCase2Y15YV0LogArg = barrierComplex (51 / 25) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV0LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV0_arg_regular :
    (barrierCase2Y15YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV0LogArg).re := by
  rw [barrierCase2Y15YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y15YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (2601 / 2500) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y15YV0LogArg (2) (0) (2601 / 2500) (51 / 25) (0 / 1)
  have hratio : ((0 / 1) / (51 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (2601 / 2500) (0 / 1) <
      (-108362745619 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-108362745619 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y15YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (2601 / 2500) (0 / 1) : ℚ) : ℝ) <
      (-108362745619 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV1_arg_eq :
    barrierCase2Y15YV1LogArg = barrierComplex (1501 / 625) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV1LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV1_arg_regular :
    (barrierCase2Y15YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV1LogArg).re := by
  rw [barrierCase2Y15YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y15YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (2253001 / 1562500) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y15YV1LogArg (2) (0) (2253001 / 1562500) (1501 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1501 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (2253001 / 1562500) (0 / 1) <
      (-39002576960 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-39002576960 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y15YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (2253001 / 1562500) (0 / 1) : ℚ) : ℝ) <
      (-39002576960 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV2_arg_eq :
    barrierCase2Y15YV2LogArg = barrierComplex (834 / 625) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV2LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV2_arg_regular :
    (barrierCase2Y15YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV2LogArg).re := by
  rw [barrierCase2Y15YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y15YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (695556 / 390625) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y15YV2LogArg (0) (0) (695556 / 390625) (834 / 625) (0 / 1)
  have hratio : ((0 / 1) / (834 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (695556 / 390625) (0 / 1) <
      (-7343008760 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-7343008760 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y15YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (695556 / 390625) (0 / 1) : ℚ) : ℝ) <
      (-7343008760 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV3_arg_eq :
    barrierCase2Y15YV3LogArg = barrierComplex (571 / 400) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV3LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV3_arg_regular :
    (barrierCase2Y15YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV3LogArg).re := by
  rw [barrierCase2Y15YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y15YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (326041 / 320000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y15YV3LogArg (1) (0) (326041 / 320000) (571 / 400) (0 / 1)
  have hratio : ((0 / 1) / (571 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (326041 / 320000) (0 / 1) <
      (17556460921 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (17556460921 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y15YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (326041 / 320000) (0 / 1) : ℚ) : ℝ) <
      (17556460921 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV4_arg_eq :
    barrierCase2Y15YV4LogArg = barrierComplex (46133 / 31250) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV4LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV4_arg_regular :
    (barrierCase2Y15YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV4LogArg).re := by
  rw [barrierCase2Y15YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y15YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (2128253689 / 1953125000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y15YV4LogArg (1) (0) (2128253689 / 1953125000) (46133 / 31250) (0 / 1)
  have hratio : ((0 / 1) / (46133 / 31250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (2128253689 / 1953125000) (0 / 1) <
      (-45253784909 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-45253784909 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y15YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (2128253689 / 1953125000) (0 / 1) : ℚ) : ℝ) <
      (-45253784909 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV5_arg_eq :
    barrierCase2Y15YV5LogArg = barrierComplex (979 / 2500) (-39 / 100) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV5LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV5_arg_regular :
    (barrierCase2Y15YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV5LogArg).re := by
  rw [barrierCase2Y15YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y15YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (954533 / 781250) (2 / 977) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y15YV5LogArg (-2) (-1) (954533 / 781250) (977 / 1250) (1 / 625)
  have hratio : ((1 / 625) / (977 / 1250) : ℚ) = (2 / 977) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (954533 / 781250) (2 / 977) <
      (-69830598176 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-69830598176 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y15YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (954533 / 781250) (2 / 977) : ℚ) : ℝ) <
      (-69830598176 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y15YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV7_arg_eq :
    barrierCase2Y15YV7LogArg = barrierComplex (19 / 100) (-9 / 20) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV7LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV7_arg_regular :
    (barrierCase2Y15YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV7LogArg).re := by
  rw [barrierCase2Y15YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y15YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-1) (1193 / 625) (-13 / 32) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y15YV7LogArg (-3) (-1) (1193 / 625) (16 / 25) (-13 / 50)
  have hratio : ((-13 / 50) / (16 / 25) : ℚ) = (-13 / 32) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-1) (1193 / 625) (-13 / 32) <
      (-289074561750 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-289074561750 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y15YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-3) (-1) (1193 / 625) (-13 / 32) : ℚ) : ℝ) <
      (-289074561750 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV9_arg_eq :
    barrierCase2Y15YV9LogArg = barrierComplex (3519 / 40000) (-191 / 400) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV9LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV9_arg_regular :
    (barrierCase2Y15YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV9LogArg).re := by
  rw [barrierCase2Y15YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y15YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (377193361 / 200000000) (3519 / 19100) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y15YV9LogArg (-3) (-2) (377193361 / 200000000) (191 / 200) (3519 / 20000)
  have hratio : ((3519 / 20000) / (191 / 200) : ℚ) = (3519 / 19100) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (377193361 / 200000000) (3519 / 19100) <
      (58526265577 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (58526265577 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y15YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (377193361 / 200000000) (3519 / 19100) : ℚ) : ℝ) <
      (58526265577 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y15YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y15 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y15YV11_arg_eq :
    barrierCase2Y15YV11LogArg = barrierComplex (496 / 15625) (-123 / 250) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y15YV11LogArg, Case2PointData.Y15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y15YV11_arg_regular :
    (barrierCase2Y15YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y15YV11LogArg).re := by
  rw [barrierCase2Y15YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y15YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y15YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y15YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (474749378 / 244140625) (992 / 15375) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y15YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y15YV11LogArg (-3) (-2) (474749378 / 244140625) (123 / 125) (992 / 15625)
  have hratio : ((992 / 15625) / (123 / 125) : ℚ) = (992 / 15375) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y15YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y15YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (474749378 / 244140625) (992 / 15375) <
      (-156292780417 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y15YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-156292780417 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y15YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y15YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (474749378 / 244140625) (992 / 15375) : ℚ) : ℝ) <
      (-156292780417 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y15_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y15 : ℝ))).sum <
      (-1095749004859 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y15 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y15 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y15YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y15YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y15YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y15YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y15YV0_log_upper,
    barrierCase2Y15YV1_log_upper,
    barrierCase2Y15YV2_log_upper,
    barrierCase2Y15YV3_log_upper,
    barrierCase2Y15YV4_log_upper,
    barrierCase2Y15YV5_log_upper,
    barrierCase2Y15YV7_log_upper,
    barrierCase2Y15YV9_log_upper,
    barrierCase2Y15YV11_log_upper]

private theorem barrierCase2Y15_approx_upper :
    barrierCase2YApproxRat Y15 (-2) (-1) (1 / 1) (3 / 2) + (-1095749004859 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y15_lt : barrierCase2Y (Y15 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y15 : ℝ)| ≤ 1 := by norm_num [Y15]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y15 hx
    (-2) (-1) (1 / 1) (3 / 2)
    Y15_normalizations.1 Y15_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y15 (-2) (-1) (1 / 1) (3 / 2) : ℚ) : ℝ) +
      (-1095749004859 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y15_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y15_YV_tail_upper]

end InternalCatalan

end

end OAI
