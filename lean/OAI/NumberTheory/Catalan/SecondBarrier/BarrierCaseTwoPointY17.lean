import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y17YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV0_arg_eq :
    barrierCase2Y17YV0LogArg = barrierComplex (71 / 25) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV0LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV0_arg_regular :
    (barrierCase2Y17YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV0LogArg).re := by
  rw [barrierCase2Y17YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y17YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (5041 / 5000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y17YV0LogArg (3) (0) (5041 / 5000) (71 / 25) (0 / 1)
  have hratio : ((0 / 1) / (71 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (5041 / 5000) (0 / 1) <
      (-158649980315 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-158649980315 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y17YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (5041 / 5000) (0 / 1) : ℚ) : ℝ) <
      (-158649980315 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV1_arg_eq :
    barrierCase2Y17YV1LogArg = barrierComplex (2101 / 625) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV1LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV1_arg_regular :
    (barrierCase2Y17YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV1LogArg).re := by
  rw [barrierCase2Y17YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y17YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (4414201 / 3125000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y17YV1LogArg (3) (0) (4414201 / 3125000) (2101 / 625) (0 / 1)
  have hratio : ((0 / 1) / (2101 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (4414201 / 3125000) (0 / 1) <
      (-53972709144 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-53972709144 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y17YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (4414201 / 3125000) (0 / 1) : ℚ) : ℝ) <
      (-53972709144 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV2_arg_eq :
    barrierCase2Y17YV2LogArg = barrierComplex (284 / 625) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV2LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV2_arg_regular :
    (barrierCase2Y17YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV2LogArg).re := by
  rw [barrierCase2Y17YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y17YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (645248 / 390625) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y17YV2LogArg (-3) (0) (645248 / 390625) (284 / 625) (0 / 1)
  have hratio : ((0 / 1) / (284 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (645248 / 390625) (0 / 1) <
      (20077524460 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (20077524460 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y17YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-3) (0) (645248 / 390625) (0 / 1) : ℚ) : ℝ) <
      (20077524460 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV3_arg_eq :
    barrierCase2Y17YV3LogArg = barrierComplex (191 / 400) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV3LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV3_arg_regular :
    (barrierCase2Y17YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV3LogArg).re := by
  rw [barrierCase2Y17YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y17YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (36481 / 20000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y17YV3LogArg (-3) (0) (36481 / 20000) (191 / 400) (0 / 1)
  have hratio : ((0 / 1) / (191 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (36481 / 20000) (0 / 1) <
      (-36461592462 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-36461592462 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y17YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-3) (0) (36481 / 20000) (0 / 1) : ℚ) : ℝ) <
      (-36461592462 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV4_arg_eq :
    barrierCase2Y17YV4LogArg = barrierComplex (15383 / 31250) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV4LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV4_arg_regular :
    (barrierCase2Y17YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV4LogArg).re := by
  rw [barrierCase2Y17YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y17YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (473273378 / 244140625) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y17YV4LogArg (-3) (0) (473273378 / 244140625) (15383 / 31250) (0 / 1)
  have hratio : ((0 / 1) / (15383 / 31250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (473273378 / 244140625) (0 / 1) <
      (82344428119 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (82344428119 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y17YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-3) (0) (473273378 / 244140625) (0 / 1) : ℚ) : ℝ) <
      (82344428119 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV5_arg_eq :
    barrierCase2Y17YV5LogArg = barrierComplex (979 / 2500) (-117 / 100) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV5LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV5_arg_regular :
    (barrierCase2Y17YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV5LogArg).re := by
  rw [barrierCase2Y17YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y17YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-1) (4757033 / 3125000) (-973 / 1952) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y17YV5LogArg (0) (-1) (4757033 / 3125000) (976 / 625) (-973 / 1250)
  have hratio : ((-973 / 1250) / (976 / 625) : ℚ) = (-973 / 1952) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-1) (4757033 / 3125000) (-973 / 1952) <
      (-268493233385 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-268493233385 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y17YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-1) (4757033 / 3125000) (-973 / 1952) : ℚ) : ℝ) <
      (-268493233385 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y17YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV7_arg_eq :
    barrierCase2Y17YV7LogArg = barrierComplex (19 / 100) (-27 / 20) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV7LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV7_arg_regular :
    (barrierCase2Y17YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV7LogArg).re := by
  rw [barrierCase2Y17YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y17YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (9293 / 5000) (19 / 135) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y17YV7LogArg (0) (-2) (9293 / 5000) (27 / 10) (19 / 50)
  have hratio : ((19 / 50) / (27 / 10) : ℚ) = (19 / 135) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (9293 / 5000) (19 / 135) <
      (-167431980737 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-167431980737 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y17YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (9293 / 5000) (19 / 135) : ℚ) : ℝ) <
      (-167431980737 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV9_arg_eq :
    barrierCase2Y17YV9LogArg = barrierComplex (3519 / 40000) (-573 / 400) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV9LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV9_arg_regular :
    (barrierCase2Y17YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV9LogArg).re := by
  rw [barrierCase2Y17YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y17YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3295673361 / 3200000000) (1173 / 19100) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y17YV9LogArg (1) (-2) (3295673361 / 3200000000) (573 / 200) (3519 / 20000)
  have hratio : ((3519 / 20000) / (573 / 200) : ℚ) = (1173 / 19100) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3295673361 / 3200000000) (1173 / 19100) <
      (101997338404 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (101997338404 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y17YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3295673361 / 3200000000) (1173 / 19100) : ℚ) : ℝ) <
      (101997338404 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y17YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y17 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y17YV11_arg_eq :
    barrierCase2Y17YV11LogArg = barrierComplex (496 / 15625) (-369 / 250) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y17YV11LogArg, Case2PointData.Y17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y17YV11_arg_regular :
    (barrierCase2Y17YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y17YV11LogArg).re := by
  rw [barrierCase2Y17YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y17YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y17YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y17YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (2128499689 / 1953125000) (992 / 46125) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y17YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y17YV11LogArg (1) (-2) (2128499689 / 1953125000) (369 / 125) (992 / 15625)
  have hratio : ((992 / 15625) / (369 / 125) : ℚ) = (992 / 46125) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y17YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y17YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (2128499689 / 1953125000) (992 / 46125) <
      (-172224264984 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y17YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-172224264984 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y17YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y17YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (2128499689 / 1953125000) (992 / 46125) : ℚ) : ℝ) <
      (-172224264984 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y17_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y17 : ℝ))).sum <
      (-1158966610746 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y17 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y17 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y17YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y17YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y17YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y17YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y17YV0_log_upper,
    barrierCase2Y17YV1_log_upper,
    barrierCase2Y17YV2_log_upper,
    barrierCase2Y17YV3_log_upper,
    barrierCase2Y17YV4_log_upper,
    barrierCase2Y17YV5_log_upper,
    barrierCase2Y17YV7_log_upper,
    barrierCase2Y17YV9_log_upper,
    barrierCase2Y17YV11_log_upper]

private theorem barrierCase2Y17_approx_upper :
    barrierCase2YApproxRat Y17 (-1) (-2) (3 / 2) (1 / 1) + (-1158966610746 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y17_lt : barrierCase2Y (Y17 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y17 : ℝ)| ≤ 1 := by norm_num [Y17]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y17 hx
    (-1) (-2) (3 / 2) (1 / 1)
    Y17_normalizations.1 Y17_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y17 (-1) (-2) (3 / 2) (1 / 1) : ℚ) : ℝ) +
      (-1158966610746 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y17_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y17_YV_tail_upper]

end InternalCatalan

end

end OAI
