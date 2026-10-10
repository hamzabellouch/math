import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y10YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV0_arg_eq :
    barrierCase2Y10YV0LogArg = barrierComplex (19127037851 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV0LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV0_arg_regular :
    (barrierCase2Y10YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV0LogArg).re := by
  rw [barrierCase2Y10YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y10YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (365843576953586698201 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y10YV0LogArg (3) (0) (365843576953586698201 / 312500000000000000000) (19127037851 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (19127037851 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (365843576953586698201 / 312500000000000000000) (0 / 1) <
      (-170006437482 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-170006437482 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y10YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (365843576953586698201 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-170006437482 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV1_arg_eq :
    barrierCase2Y10YV1LogArg = barrierComplex (56656113553 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV1LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV1_arg_regular :
    (barrierCase2Y10YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV1LogArg).re := by
  rw [barrierCase2Y10YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y10YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (3209915202930430283809 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y10YV1LogArg (3) (0) (3209915202930430283809 / 1953125000000000000000) (56656113553 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (56656113553 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (3209915202930430283809 / 1953125000000000000000) (0 / 1) <
      (-57343091509 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-57343091509 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y10YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (3209915202930430283809 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-57343091509 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV2_arg_eq :
    barrierCase2Y10YV2LogArg = barrierComplex (13252583639 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV2LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV2_arg_regular :
    (barrierCase2Y10YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV2LogArg).re := by
  rw [barrierCase2Y10YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y10YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-5) (0) (175630973108690482321 / 122070312500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y10YV2LogArg (-5) (0) (175630973108690482321 / 122070312500000000000) (13252583639 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (13252583639 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-5) (0) (175630973108690482321 / 122070312500000000000) (0 / 1) <
      (39478461985 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (39478461985 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y10YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-5) (0) (175630973108690482321 / 122070312500000000000) (0 / 1) : ℚ) : ℝ) <
      (39478461985 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV3_arg_eq :
    barrierCase2Y10YV3LogArg = barrierComplex (21586280831 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV3LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV3_arg_regular :
    (barrierCase2Y10YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV3LogArg).re := by
  rw [barrierCase2Y10YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y10YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-5) (0) (465967520114798050561 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y10YV3LogArg (-5) (0) (465967520114798050561 / 312500000000000000000) (21586280831 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (21586280831 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-5) (0) (465967520114798050561 / 312500000000000000000) (0 / 1) <
      (-75622814611 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-75622814611 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y10YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-5) (0) (465967520114798050561 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-75622814611 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV4_arg_eq :
    barrierCase2Y10YV4LogArg = barrierComplex (138284344327 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV4LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV4_arg_regular :
    (barrierCase2Y10YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV4LogArg).re := by
  rw [barrierCase2Y10YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y10YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-5) (0) (19122559885948297082929 / 12207031250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y10YV4LogArg (-5) (0) (19122559885948297082929 / 12207031250000000000000) (138284344327 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (138284344327 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-5) (0) (19122559885948297082929 / 12207031250000000000000) (0 / 1) <
      (175252883105 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (175252883105 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y10YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-5) (0) (19122559885948297082929 / 12207031250000000000000) (0 / 1) : ℚ) : ℝ) <
      (175252883105 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV5_arg_eq :
    barrierCase2Y10YV5LogArg = barrierComplex (979 / 2500) (-346204476189 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV5LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV5_arg_regular :
    (barrierCase2Y10YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV5LogArg).re := by
  rw [barrierCase2Y10YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y10YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (129441949333299867963721 / 125000000000000000000000) (8900000000 / 31473134199) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y10YV5LogArg (1) (-2) (129441949333299867963721 / 125000000000000000000000) (346204476189 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (346204476189 / 125000000000) : ℚ) = (8900000000 / 31473134199) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (129441949333299867963721 / 125000000000000000000000) (8900000000 / 31473134199) <
      (-298569860226 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-298569860226 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y10YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (129441949333299867963721 / 125000000000000000000000) (8900000000 / 31473134199) : ℚ) : ℝ) <
      (-298569860226 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y10YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV7_arg_eq :
    barrierCase2Y10YV7LogArg = barrierComplex (19 / 100) (-79893340659 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV7LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV7_arg_regular :
    (barrierCase2Y10YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV7LogArg).re := by
  rw [barrierCase2Y10YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y10YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (6473195881655022554281 / 5000000000000000000000) (9500000000 / 79893340659) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y10YV7LogArg (1) (-2) (6473195881655022554281 / 5000000000000000000000) (79893340659 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (79893340659 / 25000000000) : ℚ) = (9500000000 / 79893340659) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (6473195881655022554281 / 5000000000000000000000) (9500000000 / 79893340659) <
      (-144694392495 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-144694392495 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y10YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (6473195881655022554281 / 5000000000000000000000) (9500000000 / 79893340659) : ℚ) : ℝ) <
      (-144694392495 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV9_arg_eq :
    barrierCase2Y10YV9LogArg = barrierComplex (3519 / 40000) (-1695514229541 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV9LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV9_arg_regular :
    (barrierCase2Y10YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV9LogArg).re := by
  rw [barrierCase2Y10YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y10YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2882508103201010837070681 / 2000000000000000000000000) (9775000000 / 188390469949) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y10YV9LogArg (1) (-2) (2882508103201010837070681 / 2000000000000000000000000) (1695514229541 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1695514229541 / 500000000000) : ℚ) = (9775000000 / 188390469949) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2882508103201010837070681 / 2000000000000000000000000) (9775000000 / 188390469949) <
      (108186418689 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (108186418689 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y10YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2882508103201010837070681 / 2000000000000000000000000) (9775000000 / 188390469949) : ℚ) : ℝ) <
      (108186418689 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y10YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y10 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y10YV11_arg_eq :
    barrierCase2Y10YV11LogArg = barrierComplex (496 / 15625) (-1091875655673 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y10YV11LogArg, Case2PointData.Y10, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y10YV11_arg_regular :
    (barrierCase2Y10YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y10YV11LogArg).re := by
  rw [barrierCase2Y10YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y10YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y10YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y10YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1192586073051343657082929 / 781250000000000000000000) (19840000000 / 1091875655673) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y10YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y10YV11LogArg (1) (-2) (1192586073051343657082929 / 781250000000000000000000) (1091875655673 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (1091875655673 / 312500000000) : ℚ) = (19840000000 / 1091875655673) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y10YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y10YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1192586073051343657082929 / 781250000000000000000000) (19840000000 / 1091875655673) <
      (-174317869129 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y10YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-174317869129 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y10YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y10YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1192586073051343657082929 / 781250000000000000000000) (19840000000 / 1091875655673) : ℚ) : ℝ) <
      (-174317869129 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y10_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y10 : ℝ))).sum <
      (-1107032404834 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y10 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y10 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y10YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y10YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y10YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y10YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y10YV0_log_upper,
    barrierCase2Y10YV1_log_upper,
    barrierCase2Y10YV2_log_upper,
    barrierCase2Y10YV3_log_upper,
    barrierCase2Y10YV4_log_upper,
    barrierCase2Y10YV5_log_upper,
    barrierCase2Y10YV7_log_upper,
    barrierCase2Y10YV9_log_upper,
    barrierCase2Y10YV11_log_upper]

private theorem barrierCase2Y10_approx_upper :
    barrierCase2YApproxRat Y10 (-1) (-4) (8877037851 / 5000000000) (1122962149 / 625000000) + (-1107032404834 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y10_lt : barrierCase2Y (Y10 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y10 : ℝ)| ≤ 1 := by norm_num [Y10]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y10 hx
    (-1) (-4) (8877037851 / 5000000000) (1122962149 / 625000000)
    Y10_normalizations.1 Y10_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y10 (-1) (-4) (8877037851 / 5000000000) (1122962149 / 625000000) : ℚ) : ℝ) +
      (-1107032404834 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y10_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y10_YV_tail_upper]

end InternalCatalan

end

end OAI
