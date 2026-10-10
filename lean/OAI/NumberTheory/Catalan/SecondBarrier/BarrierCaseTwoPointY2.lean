import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y2YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV0_arg_eq :
    barrierCase2Y2YV0LogArg = barrierComplex (5507476441 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV0LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV0_arg_regular :
    (barrierCase2Y2YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV0LogArg).re := by
  rw [barrierCase2Y2YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y2YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (30332296748170026481 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y2YV0LogArg (1) (0) (30332296748170026481 / 19531250000000000000) (5507476441 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5507476441 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (30332296748170026481 / 19531250000000000000) (0 / 1) <
      (-86129709264 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-86129709264 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y2YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (30332296748170026481 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-86129709264 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV1_arg_eq :
    barrierCase2Y2YV1LogArg = barrierComplex (16159929323 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV1LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV1_arg_regular :
    (barrierCase2Y2YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV1LogArg).re := by
  rw [barrierCase2Y2YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y2YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (261143315724355238329 / 244140625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y2YV1LogArg (2) (0) (261143315724355238329 / 244140625000000000000) (16159929323 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (16159929323 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (261143315724355238329 / 244140625000000000000) (0 / 1) <
      (-32355109643 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-32355109643 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y2YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (261143315724355238329 / 244140625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-32355109643 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV2_arg_eq :
    barrierCase2Y2YV2LogArg = barrierComplex (51242759149 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV2LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV2_arg_regular :
    (barrierCase2Y2YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV2LogArg).re := by
  rw [barrierCase2Y2YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y2YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2625820365202423204201 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y2YV2LogArg (1) (0) (2625820365202423204201 / 1953125000000000000000) (51242759149 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (51242759149 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2625820365202423204201 / 1953125000000000000000) (0 / 1) <
      (-12588391727 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-12588391727 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y2YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2625820365202423204201 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-12588391727 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV3_arg_eq :
    barrierCase2Y2YV3LogArg = barrierComplex (87857947621 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV3LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV3_arg_regular :
    (barrierCase2Y2YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV3LogArg).re := by
  rw [barrierCase2Y2YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y2YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (7719018960174379559641 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y2YV3LogArg (1) (0) (7719018960174379559641 / 5000000000000000000000) (87857947621 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (87857947621 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (7719018960174379559641 / 5000000000000000000000) (0 / 1) <
      (27805172683 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (27805172683 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y2YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (7719018960174379559641 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (27805172683 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV4_arg_eq :
    barrierCase2Y2YV4LogArg = barrierComplex (568035397757 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV4LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV4_arg_regular :
    (barrierCase2Y2YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV4LogArg).re := by
  rw [barrierCase2Y2YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y2YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (322664213104953200631049 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y2YV4LogArg (1) (0) (322664213104953200631049 / 195312500000000000000000) (568035397757 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (568035397757 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (322664213104953200631049 / 195312500000000000000000) (0 / 1) <
      (-69427697507 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-69427697507 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y2YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (322664213104953200631049 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-69427697507 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV5_arg_eq :
    barrierCase2Y2YV5LogArg = barrierComplex (979 / 2500) (-14916581199 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV5LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV5_arg_regular :
    (barrierCase2Y2YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV5LogArg).re := by
  rw [barrierCase2Y2YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y2YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2618606894666360277601 / 1953125000000000000000) (-14916581199 / 48950000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y2YV5LogArg (-3) (0) (2618606894666360277601 / 1953125000000000000000) (979 / 2500) (-14916581199 / 125000000000)
  have hratio : ((-14916581199 / 125000000000) / (979 / 2500) : ℚ) = (-14916581199 / 48950000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2618606894666360277601 / 1953125000000000000000) (-14916581199 / 48950000000) <
      (64773645597 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (64773645597 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y2YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2618606894666360277601 / 1953125000000000000000) (-14916581199 / 48950000000) : ℚ) : ℝ) <
      (64773645597 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y2YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV7_arg_eq :
    barrierCase2Y2YV7LogArg = barrierComplex (19 / 100) (-3442287969 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV7LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV7_arg_regular :
    (barrierCase2Y2YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV7LogArg).re := by
  rw [barrierCase2Y2YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y2YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (-1) (34411846461522144961 / 19531250000000000000) (68826949 / 431173051) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y2YV7LogArg (-5) (-1) (34411846461522144961 / 19531250000000000000) (8192287969 / 25000000000) (1307712031 / 25000000000)
  have hratio : ((1307712031 / 25000000000) / (8192287969 / 25000000000) : ℚ) = (68826949 / 431173051) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (-1) (34411846461522144961 / 19531250000000000000) (68826949 / 431173051) <
      (-321829896484 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-321829896484 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y2YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (-1) (34411846461522144961 / 19531250000000000000) (68826949 / 431173051) : ℚ) : ℝ) <
      (-321829896484 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV9_arg_eq :
    barrierCase2Y2YV9LogArg = barrierComplex (3519 / 40000) (-73053000231 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV9LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV9_arg_regular :
    (barrierCase2Y2YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV9LogArg).re := by
  rw [barrierCase2Y2YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y2YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-6) (-1) (7271640999000486053361 / 3906250000000000000000) (-9688500077 / 39013500077) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y2YV9LogArg (-6) (-1) (7271640999000486053361 / 3906250000000000000000) (117040500231 / 500000000000) (-29065500231 / 500000000000)
  have hratio : ((-29065500231 / 500000000000) / (117040500231 / 500000000000) : ℚ) = (-9688500077 / 39013500077) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-6) (-1) (7271640999000486053361 / 3906250000000000000000) (-9688500077 / 39013500077) <
      (2081639060 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (2081639060 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y2YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-6) (-1) (7271640999000486053361 / 3906250000000000000000) (-9688500077 / 39013500077) : ℚ) : ℝ) <
      (2081639060 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y2YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y2 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y2YV11_arg_eq :
    barrierCase2Y2YV11LogArg = barrierComplex (496 / 15625) (-47044602243 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y2YV11LogArg, Case2PointData.Y2, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y2YV11_arg_regular :
    (barrierCase2Y2YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y2YV11LogArg).re := by
  rw [barrierCase2Y2YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y2YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y2YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y2YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-6) (-2) (2311601000202080631049 / 1525878906250000000000) (9920000000 / 47044602243) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y2YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y2YV11LogArg (-6) (-2) (2311601000202080631049 / 1525878906250000000000) (47044602243 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (47044602243 / 156250000000) : ℚ) = (9920000000 / 47044602243) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y2YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y2YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-6) (-2) (2311601000202080631049 / 1525878906250000000000) (9920000000 / 47044602243) <
      (-128756724331 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y2YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-128756724331 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y2YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y2YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-6) (-2) (2311601000202080631049 / 1525878906250000000000) (9920000000 / 47044602243) : ℚ) : ℝ) <
      (-128756724331 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y2_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y2 : ℝ))).sum <
      (-940158407774 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y2 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y2 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y2YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y2YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y2YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y2YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y2YV0_log_upper,
    barrierCase2Y2YV1_log_upper,
    barrierCase2Y2YV2_log_upper,
    barrierCase2Y2YV3_log_upper,
    barrierCase2Y2YV4_log_upper,
    barrierCase2Y2YV5_log_upper,
    barrierCase2Y2YV7_log_upper,
    barrierCase2Y2YV9_log_upper,
    barrierCase2Y2YV11_log_upper]

private theorem barrierCase2Y2_approx_upper :
    barrierCase2YApproxRat Y2 (-4) (-1) (382476441 / 312500000) (4617523559 / 2500000000) + (-940158407774 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y2_lt : barrierCase2Y (Y2 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y2 : ℝ)| ≤ 1 := by norm_num [Y2]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y2 hx
    (-4) (-1) (382476441 / 312500000) (4617523559 / 2500000000)
    Y2_normalizations.1 Y2_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y2 (-4) (-1) (382476441 / 312500000) (4617523559 / 2500000000) : ℚ) : ℝ) +
      (-940158407774 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y2_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y2_YV_tail_upper]

end InternalCatalan

end

end OAI
