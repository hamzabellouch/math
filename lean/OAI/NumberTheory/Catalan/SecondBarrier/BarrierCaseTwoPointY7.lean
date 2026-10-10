import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y7YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV0_arg_eq :
    barrierCase2Y7YV0LogArg = barrierComplex (7907378997 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV0LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV0_arg_regular :
    (barrierCase2Y7YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV0LogArg).re := by
  rw [barrierCase2Y7YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y7YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (62526642602196726009 / 39062500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y7YV0LogArg (2) (0) (62526642602196726009 / 39062500000000000000) (7907378997 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (7907378997 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (62526642602196726009 / 39062500000000000000) (0 / 1) <
      (-141103712990 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-141103712990 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y7YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (62526642602196726009 / 39062500000000000000) (0 / 1) : ℚ) : ℝ) <
      (-141103712990 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV1_arg_eq :
    barrierCase2Y7YV1LogArg = barrierComplex (23359636991 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV1LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV1_arg_regular :
    (barrierCase2Y7YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV1LogArg).re := by
  rw [barrierCase2Y7YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y7YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (545672640351295534081 / 488281250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y7YV1LogArg (3) (0) (545672640351295534081 / 488281250000000000000) (23359636991 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (23359636991 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (545672640351295534081 / 488281250000000000000) (0 / 1) <
      (-48758368462 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-48758368462 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y7YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (545672640351295534081 / 488281250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-48758368462 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV2_arg_eq :
    barrierCase2Y7YV2LogArg = barrierComplex (24843831033 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV2LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV2_arg_regular :
    (barrierCase2Y7YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV2LogArg).re := by
  rw [barrierCase2Y7YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y7YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-1) (0) (617215940396253847089 / 488281250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y7YV2LogArg (-1) (0) (617215940396253847089 / 488281250000000000000) (24843831033 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (24843831033 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-1) (0) (617215940396253847089 / 488281250000000000000) (0 / 1) <
      (5839395075 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (5839395075 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y7YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-1) (0) (617215940396253847089 / 488281250000000000000) (0 / 1) : ℚ) : ℝ) <
      (5839395075 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV3_arg_eq :
    barrierCase2Y7YV3LogArg = barrierComplex (42259799057 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV3LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV3_arg_regular :
    (barrierCase2Y7YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV3LogArg).re := by
  rw [barrierCase2Y7YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y7YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-1) (0) (1785890616338018089249 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y7YV3LogArg (-1) (0) (1785890616338018089249 / 1250000000000000000000) (42259799057 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (42259799057 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-1) (0) (1785890616338018089249 / 1250000000000000000000) (0 / 1) <
      (-8296036722 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-8296036722 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y7YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-1) (0) (1785890616338018089249 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-8296036722 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV4_arg_eq :
    barrierCase2Y7YV4LogArg = barrierComplex (272847383369 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV4LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV4_arg_regular :
    (barrierCase2Y7YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV4LogArg).re := by
  rw [barrierCase2Y7YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y7YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-1) (0) (74445694611310057790161 / 48828125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y7YV4LogArg (-1) (0) (74445694611310057790161 / 48828125000000000000000) (272847383369 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (272847383369 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-1) (0) (74445694611310057790161 / 48828125000000000000000) (0 / 1) <
      (15764893982 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (15764893982 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y7YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-1) (0) (74445694611310057790161 / 48828125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (15764893982 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV5_arg_eq :
    barrierCase2Y7YV5LogArg = barrierComplex (979 / 2500) (-108512780883 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV5LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV5_arg_regular :
    (barrierCase2Y7YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV5LogArg).re := by
  rw [barrierCase2Y7YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y7YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (14171126114961970259689 / 7812500000000000000000) (-59562780883 / 157462780883) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y7YV5LogArg (-1) (-1) (14171126114961970259689 / 7812500000000000000000) (157462780883 / 125000000000) (-59562780883 / 125000000000)
  have hratio : ((-59562780883 / 125000000000) / (157462780883 / 125000000000) : ℚ) = (-59562780883 / 157462780883) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (14171126114961970259689 / 7812500000000000000000) (-59562780883 / 157462780883) <
      (-213853750422 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-213853750422 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y7YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (14171126114961970259689 / 7812500000000000000000) (-59562780883 / 157462780883) : ℚ) : ℝ) <
      (-213853750422 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y7YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV7_arg_eq :
    barrierCase2Y7YV7LogArg = barrierComplex (19 / 100) (-25041410973 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV7LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV7_arg_regular :
    (barrierCase2Y7YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV7LogArg).re := by
  rw [barrierCase2Y7YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y7YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (649634763518684806729 / 625000000000000000000) (4750000000 / 25041410973) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y7YV7LogArg (0) (-2) (649634763518684806729 / 625000000000000000000) (25041410973 / 12500000000) (19 / 50)
  have hratio : ((19 / 50) / (25041410973 / 12500000000) : ℚ) = (4750000000 / 25041410973) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (649634763518684806729 / 625000000000000000000) (4750000000 / 25041410973) <
      (-205777411660 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-205777411660 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y7YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (649634763518684806729 / 625000000000000000000) (4750000000 / 25041410973) : ℚ) : ℝ) <
      (-205777411660 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV9_arg_eq :
    barrierCase2Y7YV9LogArg = barrierComplex (3519 / 40000) (-531434388427 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV9LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV9_arg_regular :
    (barrierCase2Y7YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV9LogArg).re := by
  rw [barrierCase2Y7YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y7YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (284357409359029511534329 / 250000000000000000000000) (43987500000 / 531434388427) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y7YV9LogArg (0) (-2) (284357409359029511534329 / 250000000000000000000000) (531434388427 / 250000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (531434388427 / 250000000000) : ℚ) = (43987500000 / 531434388427) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (284357409359029511534329 / 250000000000000000000000) (43987500000 / 531434388427) <
      (90794710020 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (90794710020 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y7YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (284357409359029511534329 / 250000000000000000000000) (43987500000 / 531434388427) : ℚ) : ℝ) <
      (90794710020 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y7YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y7 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y7YV11_arg_eq :
    barrierCase2Y7YV11LogArg = barrierComplex (496 / 15625) (-342232616631 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y7YV11LogArg, Case2PointData.Y7, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y7YV11_arg_regular :
    (barrierCase2Y7YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y7YV11LogArg).re := by
  rw [barrierCase2Y7YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y7YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y7YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y7YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (117221570286101017790161 / 97656250000000000000000) (9920000000 / 342232616631) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y7YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y7YV11LogArg (0) (-2) (117221570286101017790161 / 97656250000000000000000) (342232616631 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (342232616631 / 156250000000) : ℚ) = (9920000000 / 342232616631) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y7YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y7YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (117221570286101017790161 / 97656250000000000000000) (9920000000 / 342232616631) <
      (-168347735486 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y7YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-168347735486 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y7YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y7YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (117221570286101017790161 / 97656250000000000000000) (9920000000 / 342232616631) : ℚ) : ℝ) <
      (-168347735486 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y7_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y7 : ℝ))).sum <
      (-1170922204213 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y7 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y7 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y7YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y7YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y7YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y7YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y7YV0_log_upper,
    barrierCase2Y7YV1_log_upper,
    barrierCase2Y7YV2_log_upper,
    barrierCase2Y7YV3_log_upper,
    barrierCase2Y7YV4_log_upper,
    barrierCase2Y7YV5_log_upper,
    barrierCase2Y7YV7_log_upper,
    barrierCase2Y7YV9_log_upper,
    barrierCase2Y7YV11_log_upper]

private theorem barrierCase2Y7_approx_upper :
    barrierCase2YApproxRat Y7 (-1) (-2) (2782378997 / 2500000000) (2217621003 / 1250000000) + (-1170922204213 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y7_lt : barrierCase2Y (Y7 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y7 : ℝ)| ≤ 1 := by norm_num [Y7]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y7 hx
    (-1) (-2) (2782378997 / 2500000000) (2217621003 / 1250000000)
    Y7_normalizations.1 Y7_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y7 (-1) (-2) (2782378997 / 2500000000) (2217621003 / 1250000000) : ℚ) : ℝ) +
      (-1170922204213 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y7_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y7_YV_tail_upper]

end InternalCatalan

end

end OAI
