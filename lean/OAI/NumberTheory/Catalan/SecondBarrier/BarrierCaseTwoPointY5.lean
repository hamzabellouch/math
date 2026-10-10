import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y5YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV0_arg_eq :
    barrierCase2Y5YV0LogArg = barrierComplex (1662273639 / 781250000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV0LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV0_arg_regular :
    (barrierCase2Y5YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV0LogArg).re := by
  rw [barrierCase2Y5YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y5YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (2763153650914302321 / 2441406250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y5YV0LogArg (2) (0) (2763153650914302321 / 2441406250000000000) (1662273639 / 781250000) (0 / 1)
  have hratio : ((0 / 1) / (1662273639 / 781250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (2763153650914302321 / 2441406250000000000) (0 / 1) <
      (-114761096275 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-114761096275 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y5YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (2763153650914302321 / 2441406250000000000) (0 / 1) : ℚ) : ℝ) <
      (-114761096275 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV1_arg_eq :
    barrierCase2Y5YV1LogArg = barrierComplex (4896195917 / 1953125000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV1LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV1_arg_regular :
    (barrierCase2Y5YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV1LogArg).re := by
  rw [barrierCase2Y5YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y5YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (23972734457647470889 / 15258789062500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y5YV1LogArg (2) (0) (23972734457647470889 / 15258789062500000000) (4896195917 / 1953125000) (0 / 1)
  have hratio : ((0 / 1) / (4896195917 / 1953125000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (23972734457647470889 / 15258789062500000000) (0 / 1) <
      (-40912016068 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-40912016068 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y5YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (23972734457647470889 / 15258789062500000000) (0 / 1) : ℚ) : ℝ) <
      (-40912016068 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV2_arg_eq :
    barrierCase2Y5YV2LogArg = barrierComplex (9671239971 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV2LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV2_arg_regular :
    (barrierCase2Y5YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV2LogArg).re := by
  rw [barrierCase2Y5YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y5YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (93532882576668080841 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y5YV2LogArg (0) (0) (93532882576668080841 / 61035156250000000000) (9671239971 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (9671239971 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (93532882576668080841 / 61035156250000000000) (0 / 1) <
      (-5432681508 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-5432681508 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y5YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (93532882576668080841 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-5432681508 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV3_arg_eq :
    barrierCase2Y5YV3LogArg = barrierComplex (16541800859 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV3LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV3_arg_regular :
    (barrierCase2Y5YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV3LogArg).re := by
  rw [barrierCase2Y5YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y5YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (0) (0) (273631175658813137881 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y5YV3LogArg (0) (0) (273631175658813137881 / 156250000000000000000) (16541800859 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (16541800859 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (0) (0) (273631175658813137881 / 156250000000000000000) (0 / 1) <
      (13819362043 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (13819362043 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y5YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (0) (0) (273631175658813137881 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (13819362043 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV4_arg_eq :
    barrierCase2Y5YV4LogArg = barrierComplex (106904092403 / 78125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV4LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV4_arg_regular :
    (barrierCase2Y5YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV4LogArg).re := by
  rw [barrierCase2Y5YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y5YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (0) (0) (11428484972509162314409 / 6103515625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y5YV4LogArg (0) (0) (11428484972509162314409 / 6103515625000000000000) (106904092403 / 78125000000) (0 / 1)
  have hratio : ((0 / 1) / (106904092403 / 78125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (0) (0) (11428484972509162314409 / 6103515625000000000000) (0 / 1) <
      (-36437095390 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-36437095390 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y5YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (0) (0) (11428484972509162314409 / 6103515625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-36437095390 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV5_arg_eq :
    barrierCase2Y5YV5LogArg = barrierComplex (979 / 2500) (-14859921921 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV5LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV5_arg_regular :
    (barrierCase2Y5YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV5LogArg).re := by
  rw [barrierCase2Y5YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y5YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (370573685748216330241 / 244140625000000000000) (-2622421921 / 27097421921) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y5YV5LogArg (-2) (-1) (370573685748216330241 / 244140625000000000000) (27097421921 / 31250000000) (-2622421921 / 31250000000)
  have hratio : ((-2622421921 / 31250000000) / (27097421921 / 31250000000) : ℚ) = (-2622421921 / 27097421921) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (370573685748216330241 / 244140625000000000000) (-2622421921 / 27097421921) <
      (-103546555590 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-103546555590 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y5YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (370573685748216330241 / 244140625000000000000) (-2622421921 / 27097421921) : ℚ) : ℝ) <
      (-103546555590 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y5YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV7_arg_eq :
    barrierCase2Y5YV7LogArg = barrierComplex (19 / 100) (-3429212751 / 6250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV7LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV7_arg_regular :
    (barrierCase2Y5YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV7LogArg).re := by
  rw [barrierCase2Y5YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y5YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-2) (-1) (13169656341620988001 / 9765625000000000000) (-2241712751 / 4616712751) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y5YV7LogArg (-2) (-1) (13169656341620988001 / 9765625000000000000) (4616712751 / 6250000000) (-2241712751 / 6250000000)
  have hratio : ((-2241712751 / 6250000000) / (4616712751 / 6250000000) : ℚ) = (-2241712751 / 4616712751) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-2) (-1) (13169656341620988001 / 9765625000000000000) (-2241712751 / 4616712751) <
      (-271971484994 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-271971484994 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y5YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-2) (-1) (13169656341620988001 / 9765625000000000000) (-2241712751 / 4616712751) : ℚ) : ℝ) <
      (-271971484994 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV9_arg_eq :
    barrierCase2Y5YV9LogArg = barrierComplex (3519 / 40000) (-72775515049 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV9LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV9_arg_regular :
    (barrierCase2Y5YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV9LogArg).re := by
  rw [barrierCase2Y5YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y5YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-2) (-2) (5417206850412850472401 / 3906250000000000000000) (10996875000 / 72775515049) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y5YV9LogArg (-2) (-2) (5417206850412850472401 / 3906250000000000000000) (72775515049 / 62500000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (72775515049 / 62500000000) : ℚ) = (10996875000 / 72775515049) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-2) (-2) (5417206850412850472401 / 3906250000000000000000) (10996875000 / 72775515049) <
      (66900052326 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (66900052326 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y5YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-2) (-2) (5417206850412850472401 / 3906250000000000000000) (10996875000 / 72775515049) : ℚ) : ℝ) <
      (66900052326 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y5YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y5 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y5YV11_arg_eq :
    barrierCase2Y5YV11LogArg = barrierComplex (496 / 15625) (-46865907597 / 78125000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y5YV11LogArg, Case2PointData.Y5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y5YV11_arg_regular :
    (barrierCase2Y5YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y5YV11LogArg).re := by
  rw [barrierCase2Y5YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y5YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y5YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y5YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-2) (-2) (2202563694890542314409 / 1525878906250000000000) (2480000000 / 46865907597) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y5YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y5YV11LogArg (-2) (-2) (2202563694890542314409 / 1525878906250000000000) (46865907597 / 39062500000) (992 / 15625)
  have hratio : ((992 / 15625) / (46865907597 / 39062500000) : ℚ) = (2480000000 / 46865907597) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y5YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y5YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-2) (-2) (2202563694890542314409 / 1525878906250000000000) (2480000000 / 46865907597) <
      (-159578649472 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y5YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-159578649472 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y5YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y5YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-2) (-2) (2202563694890542314409 / 1525878906250000000000) (2480000000 / 46865907597) : ℚ) : ℝ) <
      (-159578649472 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y5_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y5 : ℝ))).sum <
      (-1120116802658 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y5 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y5 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y5YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y5YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y5YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y5YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y5YV0_log_upper,
    barrierCase2Y5YV1_log_upper,
    barrierCase2Y5YV2_log_upper,
    barrierCase2Y5YV3_log_upper,
    barrierCase2Y5YV4_log_upper,
    barrierCase2Y5YV5_log_upper,
    barrierCase2Y5YV7_log_upper,
    barrierCase2Y5YV9_log_upper,
    barrierCase2Y5YV11_log_upper]

private theorem barrierCase2Y5_approx_upper :
    barrierCase2YApproxRat Y5 (-2) (-1) (381023639 / 312500000) (868976361 / 625000000) + (-1120116802658 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y5_lt : barrierCase2Y (Y5 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y5 : ℝ)| ≤ 1 := by norm_num [Y5]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y5 hx
    (-2) (-1) (381023639 / 312500000) (868976361 / 625000000)
    Y5_normalizations.1 Y5_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y5 (-2) (-1) (381023639 / 312500000) (868976361 / 625000000) : ℚ) : ℝ) +
      (-1120116802658 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y5_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y5_YV_tail_upper]

end InternalCatalan

end

end OAI
