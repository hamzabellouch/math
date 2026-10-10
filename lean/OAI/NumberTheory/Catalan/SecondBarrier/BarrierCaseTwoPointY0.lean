import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y0YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV0_arg_eq :
    barrierCase2Y0YV0LogArg = barrierComplex (5213201401 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV0LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV0_arg_regular :
    (barrierCase2Y0YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV0LogArg).re := by
  rw [barrierCase2Y0YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y0YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y0YV0LogArg (1) (0) (27177468847388362801 / 19531250000000000000) (5213201401 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5213201401 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1) <
      (-77783460360 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-77783460360 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y0YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (27177468847388362801 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-77783460360 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV0_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y0YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV1_arg_eq :
    barrierCase2Y0YV1LogArg = barrierComplex (15277104203 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV1LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV1_arg_regular :
    (barrierCase2Y0YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV1LogArg).re := by
  rw [barrierCase2Y0YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y0YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y0YV1LogArg (1) (0) (233389912829320265209 / 122070312500000000000) (15277104203 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (15277104203 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1) <
      (-29854191340 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-29854191340 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y0YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (1) (0) (233389912829320265209 / 122070312500000000000) (0 / 1) : ℚ) : ℝ) <
      (-29854191340 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y0YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV2_arg_eq :
    barrierCase2Y0YV2LogArg = barrierComplex (54479784589 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV2LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV2_arg_regular :
    (barrierCase2Y0YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV2LogArg).re := by
  rw [barrierCase2Y0YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y0YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y0YV2LogArg (1) (0) (2968046928863841898921 / 1953125000000000000000) (54479784589 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (54479784589 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1) <
      (-14147585066 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-14147585066 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y0YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (2968046928863841898921 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-14147585066 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y0YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV3_arg_eq :
    barrierCase2Y0YV3LogArg = barrierComplex (93449173381 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV3LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV3_arg_regular :
    (barrierCase2Y0YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV3LogArg).re := by
  rw [barrierCase2Y0YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y0YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y0YV3LogArg (1) (0) (8732748005592198971161 / 5000000000000000000000) (93449173381 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (93449173381 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1) <
      (30848430762 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (30848430762 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y0YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (8732748005592198971161 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (30848430762 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y0YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV4_arg_eq :
    barrierCase2Y0YV4LogArg = barrierComplex (604231227677 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV4LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV4_arg_regular :
    (barrierCase2Y0YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV4LogArg).re := by
  rw [barrierCase2Y0YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y0YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y0YV4LogArg (1) (0) (365095376500054610816329 / 195312500000000000000000) (604231227677 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (604231227677 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1) <
      (-76604606631 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-76604606631 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y0YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (365095376500054610816329 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-76604606631 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y0YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV5_arg_eq :
    barrierCase2Y0YV5LogArg = barrierComplex (979 / 2500) (-3439854639 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV5LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV5_arg_regular :
    (barrierCase2Y0YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV5LogArg).re := by
  rw [barrierCase2Y0YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y0YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y0YV5LogArg (-3) (0) (2407935099937449820321 / 1953125000000000000000) (979 / 2500) (-3439854639 / 125000000000)
  have hratio : ((-3439854639 / 125000000000) / (979 / 2500) : ℚ) = (-3439854639 / 48950000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000) <
      (113860922989 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (113860922989 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y0YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (2407935099937449820321 / 1953125000000000000000) (-3439854639 / 48950000000) : ℚ) : ℝ) <
      (113860922989 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y0YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV7_arg_eq :
    barrierCase2Y0YV7LogArg = barrierComplex (19 / 100) (-793812609 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV7LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV7_arg_regular :
    (barrierCase2Y0YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV7LogArg).re := by
  rw [barrierCase2Y0YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y0YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y0YV7LogArg (-5) (0) (23192638458207386881 / 19531250000000000000) (19 / 100) (-793812609 / 25000000000)
  have hratio : ((-793812609 / 25000000000) / (19 / 100) : ℚ) = (-41779611 / 250000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000) <
      (-283081837779 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-283081837779 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y0YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000) : ℚ) : ℝ) <
      (-283081837779 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV7_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y0YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV9_arg_eq :
    barrierCase2Y0YV9LogArg = barrierComplex (3519 / 40000) (-16846467591 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV9LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV9_arg_regular :
    (barrierCase2Y0YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV9LogArg).re := by
  rw [barrierCase2Y0YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y0YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (0) (2218703626544613343281 / 1953125000000000000000) (-5615489197 / 14662500000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y0YV9LogArg (-7) (0) (2218703626544613343281 / 1953125000000000000000) (3519 / 40000) (-16846467591 / 500000000000)
  have hratio : ((-16846467591 / 500000000000) / (3519 / 40000) : ℚ) = (-5615489197 / 14662500000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (0) (2218703626544613343281 / 1953125000000000000000) (-5615489197 / 14662500000) <
      (-57275131932 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-57275131932 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y0YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-7) (0) (2218703626544613343281 / 1953125000000000000000) (-5615489197 / 14662500000) : ℚ) : ℝ) <
      (-57275131932 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y0YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y0 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y0YV11_arg_eq :
    barrierCase2Y0YV11LogArg = barrierComplex (496 / 15625) (-10848772323 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y0YV11LogArg, Case2PointData.Y0, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y0YV11_arg_regular :
    (barrierCase2Y0YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y0YV11LogArg).re := by
  rw [barrierCase2Y0YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y0YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y0YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y0YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y0YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y0YV11LogArg (-9) (-1) (216102260916290816329 / 190734863281250000000) (20768772323 / 312500000000) (-928772323 / 312500000000)
  have hratio : ((-928772323 / 312500000000) / (20768772323 / 312500000000) : ℚ) = (-928772323 / 20768772323) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y0YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y0YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323) <
      (-58719191124 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y0YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-58719191124 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y0YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y0YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323) : ℚ) : ℝ) <
      (-58719191124 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y0_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y0 : ℝ))).sum <
      (-737971888327 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y0 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y0YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y0YV0_log_upper,
    barrierCase2Y0YV1_log_upper,
    barrierCase2Y0YV2_log_upper,
    barrierCase2Y0YV3_log_upper,
    barrierCase2Y0YV4_log_upper,
    barrierCase2Y0YV5_log_upper,
    barrierCase2Y0YV7_log_upper,
    barrierCase2Y0YV9_log_upper,
    barrierCase2Y0YV11_log_upper]

private theorem barrierCase2Y0_approx_upper :
    barrierCase2YApproxRat Y0 (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) + (-737971888327 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y0_lt : barrierCase2Y (Y0 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y0 : ℝ)| ≤ 1 := by norm_num [Y0]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y0 hx
    (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000)
    Y0_normalizations.1 Y0_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y0 (-6) (-1) (88201401 / 78125000) (4911798599 / 2500000000) : ℚ) : ℝ) +
      (-737971888327 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y0_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y0_YV_tail_upper]

end InternalCatalan

end

end OAI
