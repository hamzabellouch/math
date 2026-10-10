import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y13YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV0_arg_eq :
    barrierCase2Y13YV0LogArg = barrierComplex (4044545563 / 1250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV0LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV0_arg_regular :
    (barrierCase2Y13YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV0LogArg).re := by
  rw [barrierCase2Y13YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y13YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (16358348811182986969 / 12500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y13YV0LogArg (3) (0) (16358348811182986969 / 12500000000000000000) (4044545563 / 1250000000) (0 / 1)
  have hratio : ((0 / 1) / (4044545563 / 1250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (16358348811182986969 / 12500000000000000000) (0 / 1) <
      (-178473033781 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-178473033781 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y13YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (16358348811182986969 / 12500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-178473033781 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV1_arg_eq :
    barrierCase2Y13YV1LogArg = barrierComplex (11988636689 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV1LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV1_arg_regular :
    (barrierCase2Y13YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV1LogArg).re := by
  rw [barrierCase2Y13YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y13YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (143727409660836882721 / 78125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y13YV1LogArg (3) (0) (143727409660836882721 / 78125000000000000000) (11988636689 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (11988636689 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (143727409660836882721 / 78125000000000000000) (0 / 1) <
      (-59853707408 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-59853707408 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y13YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (143727409660836882721 / 78125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-59853707408 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV2_arg_eq :
    barrierCase2Y13YV2LogArg = barrierComplex (239998807 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV2LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV2_arg_regular :
    (barrierCase2Y13YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV2LogArg).re := by
  rw [barrierCase2Y13YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y13YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-12) (0) (57599427361423249 / 38146972656250000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y13YV2LogArg (-12) (0) (57599427361423249 / 38146972656250000) (239998807 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (239998807 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-12) (0) (57599427361423249 / 38146972656250000) (0 / 1) <
      (100615764101 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (100615764101 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y13YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-12) (0) (57599427361423249 / 38146972656250000) (0 / 1) : ℚ) : ℝ) <
      (100615764101 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV3_arg_eq :
    barrierCase2Y13YV3LogArg = barrierComplex (153634303 / 20000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV3LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV3_arg_regular :
    (barrierCase2Y13YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV3LogArg).re := by
  rw [barrierCase2Y13YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y13YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-15) (0) (23603499058295809 / 12207031250000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y13YV3LogArg (-15) (0) (23603499058295809 / 12207031250000000) (153634303 / 20000000000) (0 / 1)
  have hratio : ((0 / 1) / (153634303 / 20000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-15) (0) (23603499058295809 / 12207031250000000) (0 / 1) <
      (-240165629948 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-240165629948 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y13YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-15) (0) (23603499058295809 / 12207031250000000) (0 / 1) : ℚ) : ℝ) <
      (-240165629948 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV4_arg_eq :
    barrierCase2Y13YV4LogArg = barrierComplex (702895751 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV4LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV4_arg_regular :
    (barrierCase2Y13YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV4LogArg).re := by
  rw [barrierCase2Y13YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y13YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-15) (0) (494062436773854001 / 476837158203125000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y13YV4LogArg (-15) (0) (494062436773854001 / 476837158203125000) (702895751 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (702895751 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-15) (0) (494062436773854001 / 476837158203125000) (0 / 1) <
      (601920498370 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (601920498370 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y13YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-15) (0) (494062436773854001 / 476837158203125000) (0 / 1) : ℚ) : ℝ) <
      (601920498370 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV5_arg_eq :
    barrierCase2Y13YV5LogArg = barrierComplex (979 / 2500) (-77787276957 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV5LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV5_arg_regular :
    (barrierCase2Y13YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV5LogArg).re := by
  rw [barrierCase2Y13YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y13YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (6434236856385023179849 / 5000000000000000000000) (19580000000 / 77787276957) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y13YV5LogArg (1) (-2) (6434236856385023179849 / 5000000000000000000000) (77787276957 / 25000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (77787276957 / 25000000000) : ℚ) = (19580000000 / 77787276957) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (6434236856385023179849 / 5000000000000000000000) (19580000000 / 77787276957) <
      (-318939898566 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-318939898566 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y13YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (6434236856385023179849 / 5000000000000000000000) (19580000000 / 77787276957) : ℚ) : ℝ) <
      (-318939898566 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y13YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV7_arg_eq :
    barrierCase2Y13YV7LogArg = barrierComplex (19 / 100) (-17950910067 / 10000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV7LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV7_arg_regular :
    (barrierCase2Y13YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV7LogArg).re := by
  rw [barrierCase2Y13YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y13YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (325845172233521944489 / 200000000000000000000) (1900000000 / 17950910067) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y13YV7LogArg (1) (-2) (325845172233521944489 / 200000000000000000000) (17950910067 / 5000000000) (19 / 50)
  have hratio : ((19 / 50) / (17950910067 / 5000000000) : ℚ) = (1900000000 / 17950910067) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (325845172233521944489 / 200000000000000000000) (1900000000 / 17950910067) <
      (-128630585549 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-128630585549 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y13YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (325845172233521944489 / 200000000000000000000) (1900000000 / 17950910067) : ℚ) : ℝ) <
      (-128630585549 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV9_arg_eq :
    barrierCase2Y13YV9LogArg = barrierComplex (3519 / 40000) (-380958202533 / 200000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV9LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV9_arg_regular :
    (barrierCase2Y13YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV9LogArg).re := by
  rw [barrierCase2Y13YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y13YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (145438736102174247616089 / 80000000000000000000000) (5865000000 / 126986067511) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y13YV9LogArg (1) (-2) (145438736102174247616089 / 80000000000000000000000) (380958202533 / 100000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (380958202533 / 100000000000) : ℚ) = (5865000000 / 126986067511) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (145438736102174247616089 / 80000000000000000000000) (5865000000 / 126986067511) <
      (112410993994 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (112410993994 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y13YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (145438736102174247616089 / 80000000000000000000000) (5865000000 / 126986067511) : ℚ) : ℝ) <
      (112410993994 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y13YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y13 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y13YV11_arg_eq :
    barrierCase2Y13YV11LogArg = barrierComplex (496 / 15625) (-245329104249 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y13YV11LogArg, Case2PointData.Y13, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y13YV11_arg_regular :
    (barrierCase2Y13YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y13YV11LogArg).re := by
  rw [barrierCase2Y13YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y13YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y13YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y13YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (60202114415616709854001 / 31250000000000000000000) (3968000000 / 245329104249) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y13YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y13YV11LogArg (1) (-2) (60202114415616709854001 / 31250000000000000000000) (245329104249 / 62500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (245329104249 / 62500000000) : ℚ) = (3968000000 / 245329104249) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y13YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y13YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (60202114415616709854001 / 31250000000000000000000) (3968000000 / 245329104249) <
      (-175730210290 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y13YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-175730210290 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y13YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y13YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (60202114415616709854001 / 31250000000000000000000) (3968000000 / 245329104249) : ℚ) : ℝ) <
      (-175730210290 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y13_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y13 : ℝ))).sum <
      (-797735509488 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y13 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y13 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y13YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y13YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y13YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y13YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y13YV0_log_upper,
    barrierCase2Y13YV1_log_upper,
    barrierCase2Y13YV2_log_upper,
    barrierCase2Y13YV3_log_upper,
    barrierCase2Y13YV4_log_upper,
    barrierCase2Y13YV5_log_upper,
    barrierCase2Y13YV7_log_upper,
    barrierCase2Y13YV9_log_upper,
    barrierCase2Y13YV11_log_upper]

private theorem barrierCase2Y13_approx_upper :
    barrierCase2YApproxRat Y13 (-1) (-9) (1994545563 / 1000000000) (5454437 / 3906250) + (-797735509488 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y13_lt : barrierCase2Y (Y13 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y13 : ℝ)| ≤ 1 := by norm_num [Y13]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y13 hx
    (-1) (-9) (1994545563 / 1000000000) (5454437 / 3906250)
    Y13_normalizations.1 Y13_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y13 (-1) (-9) (1994545563 / 1000000000) (5454437 / 3906250) : ℚ) : ℝ) +
      (-797735509488 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y13_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y13_YV_tail_upper]

end InternalCatalan

end

end OAI
