import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y12YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV0_arg_eq :
    barrierCase2Y12YV0LogArg = barrierComplex (20088463999 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV0LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV0_arg_regular :
    (barrierCase2Y12YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV0LogArg).re := by
  rw [barrierCase2Y12YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y12YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (403546385839119072001 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y12YV0LogArg (3) (0) (403546385839119072001 / 312500000000000000000) (20088463999 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (20088463999 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (403546385839119072001 / 312500000000000000000) (0 / 1) <
      (-177460554852 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-177460554852 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y12YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (403546385839119072001 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-177460554852 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV1_arg_eq :
    barrierCase2Y12YV1LogArg = barrierComplex (59540391997 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV1LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV1_arg_regular :
    (barrierCase2Y12YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV1LogArg).re := by
  rw [barrierCase2Y12YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y12YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (3545058279156421648009 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y12YV1LogArg (3) (0) (3545058279156421648009 / 1953125000000000000000) (59540391997 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (59540391997 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (3545058279156421648009 / 1953125000000000000000) (0 / 1) <
      (-59553566042 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-59553566042 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y12YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (3545058279156421648009 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-59553566042 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV2_arg_eq :
    barrierCase2Y12YV2LogArg = barrierComplex (2676896011 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV2LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV2_arg_regular :
    (barrierCase2Y12YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV2LogArg).re := by
  rw [barrierCase2Y12YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y12YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-10) (0) (7165772253707712121 / 3814697265625000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y12YV2LogArg (-10) (0) (7165772253707712121 / 3814697265625000000) (2676896011 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (2676896011 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-10) (0) (7165772253707712121 / 3814697265625000000) (0 / 1) <
      (80192983871 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (80192983871 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y12YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-10) (0) (7165772253707712121 / 3814697265625000000) (0 / 1) : ℚ) : ℝ) <
      (80192983871 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV3_arg_eq :
    barrierCase2Y12YV3LogArg = barrierComplex (3319184019 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV3LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV3_arg_regular :
    (barrierCase2Y12YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV3LogArg).re := by
  rw [barrierCase2Y12YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y12YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-10) (0) (11016982551984992361 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y12YV3LogArg (-10) (0) (11016982551984992361 / 9765625000000000000) (3319184019 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (3319184019 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-10) (0) (11016982551984992361 / 9765625000000000000) (0 / 1) <
      (-167978444270 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-167978444270 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y12YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-10) (0) (11016982551984992361 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-167978444270 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV4_arg_eq :
    barrierCase2Y12YV4LogArg = barrierComplex (20028928123 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV4LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV4_arg_regular :
    (barrierCase2Y12YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV4LogArg).re := by
  rw [barrierCase2Y12YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y12YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-10) (0) (401157961756300303129 / 381469726562500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y12YV4LogArg (-10) (0) (401157961756300303129 / 381469726562500000000) (20028928123 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (20028928123 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-10) (0) (401157961756300303129 / 381469726562500000000) (0 / 1) <
      (399731290774 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (399731290774 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y12YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-10) (0) (401157961756300303129 / 381469726562500000000) (0 / 1) : ℚ) : ℝ) <
      (399731290774 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV5_arg_eq :
    barrierCase2Y12YV5LogArg = barrierComplex (979 / 2500) (-383700095961 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV5LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV5_arg_regular :
    (barrierCase2Y12YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV5LogArg).re := by
  rw [barrierCase2Y12YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y12YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (156810173640480608513521 / 125000000000000000000000) (97900000000 / 383700095961) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y12YV5LogArg (1) (-2) (156810173640480608513521 / 125000000000000000000000) (383700095961 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (383700095961 / 125000000000) : ℚ) = (97900000000 / 383700095961) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (156810173640480608513521 / 125000000000000000000000) (97900000000 / 383700095961) <
      (-316584760105 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-316584760105 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y12YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (156810173640480608513521 / 125000000000000000000000) (97900000000 / 383700095961) : ℚ) : ℝ) <
      (-316584760105 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y12YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV7_arg_eq :
    barrierCase2Y12YV7LogArg = barrierComplex (19 / 100) (-88546175991 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV7LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV7_arg_regular :
    (barrierCase2Y12YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV7LogArg).re := by
  rw [barrierCase2Y12YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y12YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (7930675282629144832081 / 5000000000000000000000) (9500000000 / 88546175991) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y12YV7LogArg (1) (-2) (7930675282629144832081 / 5000000000000000000000) (88546175991 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (88546175991 / 25000000000) : ℚ) = (9500000000 / 88546175991) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (7930675282629144832081 / 5000000000000000000000) (9500000000 / 88546175991) <
      (-130515225213 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-130515225213 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y12YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (7930675282629144832081 / 5000000000000000000000) (9500000000 / 88546175991) : ℚ) : ℝ) <
      (-130515225213 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV9_arg_eq :
    barrierCase2Y12YV9LogArg = barrierComplex (3519 / 40000) (-1879146623809 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV9LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV9_arg_regular :
    (barrierCase2Y12YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV9LogArg).re := by
  rw [barrierCase2Y12YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y12YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3538931634397763365668481 / 2000000000000000000000000) (87975000000 / 1879146623809) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y12YV9LogArg (1) (-2) (3538931634397763365668481 / 2000000000000000000000000) (1879146623809 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1879146623809 / 500000000000) : ℚ) = (87975000000 / 1879146623809) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3538931634397763365668481 / 2000000000000000000000000) (87975000000 / 1879146623809) <
      (111920872984 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (111920872984 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y12YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3538931634397763365668481 / 2000000000000000000000000) (87975000000 / 1879146623809) : ℚ) : ℝ) <
      (111920872984 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y12YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y12 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y12YV11_arg_eq :
    barrierCase2Y12YV11LogArg = barrierComplex (496 / 15625) (-1210131071877 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y12YV11LogArg, Case2PointData.Y12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y12YV11_arg_regular :
    (barrierCase2Y12YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y12YV11LogArg).re := by
  rw [barrierCase2Y12YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y12YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y12YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y12YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1464810836722176940303129 / 781250000000000000000000) (19840000000 / 1210131071877) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y12YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y12YV11LogArg (1) (-2) (1464810836722176940303129 / 781250000000000000000000) (1210131071877 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (1210131071877 / 312500000000) : ℚ) = (19840000000 / 1210131071877) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y12YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y12YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1464810836722176940303129 / 781250000000000000000000) (19840000000 / 1210131071877) <
      (-175566999853 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y12YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-175566999853 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y12YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y12YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1464810836722176940303129 / 781250000000000000000000) (19840000000 / 1210131071877) : ℚ) : ℝ) <
      (-175566999853 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y12_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y12 : ℝ))).sum <
      (-946560514893 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y12 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y12 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y12YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y12YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y12YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y12YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y12YV0_log_upper,
    barrierCase2Y12YV1_log_upper,
    barrierCase2Y12YV2_log_upper,
    barrierCase2Y12YV3_log_upper,
    barrierCase2Y12YV4_log_upper,
    barrierCase2Y12YV5_log_upper,
    barrierCase2Y12YV7_log_upper,
    barrierCase2Y12YV9_log_upper,
    barrierCase2Y12YV11_log_upper]

private theorem barrierCase2Y12_approx_upper :
    barrierCase2YApproxRat Y12 (-1) (-6) (9838463999 / 5000000000) (161536001 / 156250000) + (-946560514893 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y12_lt : barrierCase2Y (Y12 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y12 : ℝ)| ≤ 1 := by norm_num [Y12]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y12 hx
    (-1) (-6) (9838463999 / 5000000000) (161536001 / 156250000)
    Y12_normalizations.1 Y12_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y12 (-1) (-6) (9838463999 / 5000000000) (161536001 / 156250000) : ℚ) : ℝ) +
      (-946560514893 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y12_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y12_YV_tail_upper]

end InternalCatalan

end

end OAI
