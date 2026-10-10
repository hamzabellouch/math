import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y6YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV0_arg_eq :
    barrierCase2Y6YV0LogArg = barrierComplex (1821587387 / 781250000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV0LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV0_arg_regular :
    (barrierCase2Y6YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV0LogArg).re := by
  rw [barrierCase2Y6YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y6YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (3318180608477487769 / 2441406250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y6YV0LogArg (2) (0) (3318180608477487769 / 2441406250000000000) (1821587387 / 781250000) (0 / 1)
  have hratio : ((0 / 1) / (1821587387 / 781250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (3318180608477487769 / 2441406250000000000) (0 / 1) <
      (-128671715784 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-128671715784 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y6YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (3318180608477487769 / 2441406250000000000) (0 / 1) : ℚ) : ℝ) <
      (-128671715784 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV1_arg_eq :
    barrierCase2Y6YV1LogArg = barrierComplex (5374137161 / 1953125000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV1LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV1_arg_regular :
    (barrierCase2Y6YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV1LogArg).re := by
  rw [barrierCase2Y6YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y6YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (28881350225241139921 / 15258789062500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y6YV1LogArg (2) (0) (28881350225241139921 / 15258789062500000000) (5374137161 / 1953125000) (0 / 1)
  have hratio : ((0 / 1) / (5374137161 / 1953125000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (28881350225241139921 / 15258789062500000000) (0 / 1) <
      (-45058270586 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-45058270586 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y6YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (28881350225241139921 / 15258789062500000000) (0 / 1) : ℚ) : ℝ) <
      (-45058270586 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV2_arg_eq :
    barrierCase2Y6YV2LogArg = barrierComplex (7918788743 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV2LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV2_arg_regular :
    (barrierCase2Y6YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV2LogArg).re := by
  rw [barrierCase2Y6YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y6YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (62707215156263520049 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y6YV2LogArg (0) (0) (62707215156263520049 / 61035156250000000000) (7918788743 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (7918788743 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (62707215156263520049 / 61035156250000000000) (0 / 1) <
      (-343965805 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-343965805 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y6YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (0) (0) (62707215156263520049 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-343965805 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV3_arg_eq :
    barrierCase2Y6YV3LogArg = barrierComplex (13514839647 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV3LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV3_arg_regular :
    (barrierCase2Y6YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV3LogArg).re := by
  rw [barrierCase2Y6YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y6YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (0) (0) (182650890684123084609 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y6YV3LogArg (0) (0) (182650890684123084609 / 156250000000000000000) (13514839647 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (13514839647 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (0) (0) (182650890684123084609 / 156250000000000000000) (0 / 1) <
      (3850397850 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (3850397850 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y6YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (0) (0) (182650890684123084609 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (3850397850 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV4_arg_eq :
    barrierCase2Y6YV4LogArg = barrierComplex (87308501399 / 78125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV4LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV4_arg_regular :
    (barrierCase2Y6YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV4LogArg).re := by
  rw [barrierCase2Y6YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y6YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (0) (0) (7622774416539184957201 / 6103515625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y6YV4LogArg (0) (0) (7622774416539184957201 / 6103515625000000000000) (87308501399 / 78125000000) (0 / 1)
  have hratio : ((0 / 1) / (87308501399 / 78125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (0) (0) (7622774416539184957201 / 6103515625000000000000) (0 / 1) <
      (-12912156128 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-12912156128 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y6YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (0) (0) (7622774416539184957201 / 6103515625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-12912156128 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV5_arg_eq :
    barrierCase2Y6YV5LogArg = barrierComplex (979 / 2500) (-21073158093 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV5LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV5_arg_regular :
    (barrierCase2Y6YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV5LogArg).re := by
  rw [barrierCase2Y6YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y6YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (593834398262571396649 / 488281250000000000000) (-8835658093 / 33310658093) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y6YV5LogArg (-1) (-1) (593834398262571396649 / 488281250000000000000) (33310658093 / 31250000000) (-8835658093 / 31250000000)
  have hratio : ((-8835658093 / 31250000000) / (33310658093 / 31250000000) : ℚ) = (-8835658093 / 33310658093) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (593834398262571396649 / 488281250000000000000) (-8835658093 / 33310658093) <
      (-166954549636 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-166954549636 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y6YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (593834398262571396649 / 488281250000000000000) (-8835658093 / 33310658093) : ℚ) : ℝ) <
      (-166954549636 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y6YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV7_arg_eq :
    barrierCase2Y6YV7LogArg = barrierComplex (19 / 100) (-4863036483 / 6250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV7LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV7_arg_regular :
    (barrierCase2Y6YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV7LogArg).re := by
  rw [barrierCase2Y6YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y6YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-1) (-2) (25059280084989009289 / 19531250000000000000) (1187500000 / 4863036483) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y6YV7LogArg (-1) (-2) (25059280084989009289 / 19531250000000000000) (4863036483 / 3125000000) (19 / 50)
  have hratio : ((19 / 50) / (4863036483 / 3125000000) : ℚ) = (1187500000 / 4863036483) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-1) (-2) (25059280084989009289 / 19531250000000000000) (1187500000 / 4863036483) <
      (-235733023745 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-235733023745 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y6YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-1) (-2) (25059280084989009289 / 19531250000000000000) (1187500000 / 4863036483) : ℚ) : ℝ) <
      (-235733023745 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV9_arg_eq :
    barrierCase2Y6YV9LogArg = barrierComplex (3519 / 40000) (-103204440917 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV9LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV9_arg_regular :
    (barrierCase2Y6YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV9LogArg).re := by
  rw [barrierCase2Y6YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y6YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-1) (-2) (10772087884756168800889 / 7812500000000000000000) (10996875000 / 103204440917) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y6YV9LogArg (-1) (-2) (10772087884756168800889 / 7812500000000000000000) (103204440917 / 62500000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (103204440917 / 62500000000) : ℚ) = (10996875000 / 103204440917) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-1) (-2) (10772087884756168800889 / 7812500000000000000000) (10996875000 / 103204440917) <
      (81012419912 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (81012419912 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y6YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-1) (-2) (10772087884756168800889 / 7812500000000000000000) (10996875000 / 103204440917) : ℚ) : ℝ) <
      (81012419912 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y6YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y6 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y6YV11_arg_eq :
    barrierCase2Y6YV11LogArg = barrierComplex (496 / 15625) (-66461498601 / 78125000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y6YV11LogArg, Case2PointData.Y6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y6YV11_arg_regular :
    (barrierCase2Y6YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y6YV11LogArg).re := by
  rw [barrierCase2Y6YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y6YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y6YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y6YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-1) (-2) (4423281196290724957201 / 3051757812500000000000) (2480000000 / 66461498601) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y6YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y6YV11LogArg (-1) (-2) (4423281196290724957201 / 3051757812500000000000) (66461498601 / 39062500000) (992 / 15625)
  have hratio : ((992 / 15625) / (66461498601 / 39062500000) : ℚ) = (2480000000 / 66461498601) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y6YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y6YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-1) (-2) (4423281196290724957201 / 3051757812500000000000) (2480000000 / 66461498601) <
      (-164851781315 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y6YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-164851781315 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y6YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y6YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-1) (-2) (4423281196290724957201 / 3051757812500000000000) (2480000000 / 66461498601) : ℚ) : ℝ) <
      (-164851781315 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y6_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y6 : ℝ))).sum <
      (-1156189580021 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y6 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y6 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y6YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y6YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y6YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y6YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y6YV0_log_upper,
    barrierCase2Y6YV1_log_upper,
    barrierCase2Y6YV2_log_upper,
    barrierCase2Y6YV3_log_upper,
    barrierCase2Y6YV4_log_upper,
    barrierCase2Y6YV5_log_upper,
    barrierCase2Y6YV7_log_upper,
    barrierCase2Y6YV9_log_upper,
    barrierCase2Y6YV11_log_upper]

private theorem barrierCase2Y6_approx_upper :
    barrierCase2YApproxRat Y6 (-2) (-1) (540337387 / 312500000) (709662613 / 625000000) + (-1156189580021 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y6_lt : barrierCase2Y (Y6 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y6 : ℝ)| ≤ 1 := by norm_num [Y6]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y6 hx
    (-2) (-1) (540337387 / 312500000) (709662613 / 625000000)
    Y6_normalizations.1 Y6_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y6 (-2) (-1) (540337387 / 312500000) (709662613 / 625000000) : ℚ) : ℝ) +
      (-1156189580021 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y6_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y6_YV_tail_upper]

end InternalCatalan

end

end OAI
