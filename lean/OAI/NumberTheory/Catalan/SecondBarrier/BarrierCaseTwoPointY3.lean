import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y3YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV0_arg_eq :
    barrierCase2Y3YV0LogArg = barrierComplex (11477250753 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV0LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV0_arg_regular :
    (barrierCase2Y3YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV0LogArg).re := by
  rw [barrierCase2Y3YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y3YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (131727284847239067009 / 78125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y3YV0LogArg (1) (0) (131727284847239067009 / 78125000000000000000) (11477250753 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (11477250753 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (131727284847239067009 / 78125000000000000000) (0 / 1) <
      (-92378587958 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-92378587958 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y3YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (1) (0) (131727284847239067009 / 78125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-92378587958 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV1_arg_eq :
    barrierCase2Y3YV1LogArg = barrierComplex (33706752259 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV1LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV1_arg_regular :
    (barrierCase2Y3YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV1LogArg).re := by
  rw [barrierCase2Y3YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y3YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (1136145147849601603081 / 976562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y3YV1LogArg (2) (0) (1136145147849601603081 / 976562500000000000000) (33706752259 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (33706752259 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (1136145147849601603081 / 976562500000000000000) (0 / 1) <
      (-34225534238 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-34225534238 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y3YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (2) (0) (1136145147849601603081 / 976562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (-34225534238 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV2_arg_eq :
    barrierCase2Y3YV2LogArg = barrierComplex (97400241717 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV2LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV2_arg_regular :
    (barrierCase2Y3YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV2LogArg).re := by
  rw [barrierCase2Y3YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y3YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (9486807086530027108089 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y3YV2LogArg (1) (0) (9486807086530027108089 / 7812500000000000000000) (97400241717 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (97400241717 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (9486807086530027108089 / 7812500000000000000000) (0 / 1) <
      (-11292967125 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-11292967125 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y3YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (1) (0) (9486807086530027108089 / 7812500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-11292967125 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV3_arg_eq :
    barrierCase2Y3YV3LogArg = barrierComplex (166932235693 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV3LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV3_arg_regular :
    (barrierCase2Y3YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV3LogArg).re := by
  rw [barrierCase2Y3YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y3YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (27866371313463303190249 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y3YV3LogArg (1) (0) (27866371313463303190249 / 20000000000000000000000) (166932235693 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (166932235693 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (27866371313463303190249 / 20000000000000000000000) (0 / 1) <
      (25275693136 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (25275693136 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y3YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (1) (0) (27866371313463303190249 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (25275693136 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV4_arg_eq :
    barrierCase2Y3YV4LogArg = barrierComplex (1079208157381 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV4LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV4_arg_regular :
    (barrierCase2Y3YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV4LogArg).re := by
  rw [barrierCase2Y3YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y3YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (1164690246957693264779161 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y3YV4LogArg (1) (0) (1164690246957693264779161 / 781250000000000000000000) (1079208157381 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (1079208157381 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (1164690246957693264779161 / 781250000000000000000000) (0 / 1) <
      (-63462000008 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-63462000008 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y3YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (1) (0) (1164690246957693264779161 / 781250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-63462000008 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV5_arg_eq :
    barrierCase2Y3YV5LogArg = barrierComplex (979 / 2500) (-47862779367 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV5LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV5_arg_regular :
    (barrierCase2Y3YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV5LogArg).re := by
  rw [barrierCase2Y3YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y3YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (11875255648734120920689 / 7812500000000000000000) (-47862779367 / 97900000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y3YV5LogArg (-3) (0) (11875255648734120920689 / 7812500000000000000000) (979 / 2500) (-47862779367 / 250000000000)
  have hratio : ((-47862779367 / 250000000000) / (979 / 2500) : ℚ) = (-47862779367 / 97900000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (11875255648734120920689 / 7812500000000000000000) (-47862779367 / 97900000000) <
      (25673019079 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (25673019079 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y3YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (-3) (0) (11875255648734120920689 / 7812500000000000000000) (-47862779367 / 97900000000) : ℚ) : ℝ) <
      (25673019079 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y3YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV7_arg_eq :
    barrierCase2Y3YV7LogArg = barrierComplex (19 / 100) (-11045256777 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV7LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV7_arg_regular :
    (barrierCase2Y3YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV7LogArg).re := by
  rw [barrierCase2Y3YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y3YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-4) (-1) (212247697269864427729 / 156250000000000000000) (-1545256777 / 20545256777) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y3YV7LogArg (-4) (-1) (212247697269864427729 / 156250000000000000000) (20545256777 / 50000000000) (-1545256777 / 50000000000)
  have hratio : ((-1545256777 / 50000000000) / (20545256777 / 50000000000) : ℚ) = (-1545256777 / 20545256777) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-4) (-1) (212247697269864427729 / 156250000000000000000) (-1545256777 / 20545256777) <
      (-323123260794 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-323123260794 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y3YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (-4) (-1) (212247697269864427729 / 156250000000000000000) (-1545256777 / 20545256777) : ℚ) : ℝ) <
      (-323123260794 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV9_arg_eq :
    barrierCase2Y3YV9LogArg = barrierComplex (3519 / 40000) (-234404893823 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV9LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV9_arg_regular :
    (barrierCase2Y3YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV9LogArg).re := by
  rw [barrierCase2Y3YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y3YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-4) (-1) (62685254873171903555329 / 62500000000000000000000) (-146429893823 / 322379893823) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y3YV9LogArg (-4) (-1) (62685254873171903555329 / 62500000000000000000000) (322379893823 / 1000000000000) (-146429893823 / 1000000000000)
  have hratio : ((-146429893823 / 1000000000000) / (322379893823 / 1000000000000) : ℚ) = (-146429893823 / 322379893823) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-4) (-1) (62685254873171903555329 / 62500000000000000000000) (-146429893823 / 322379893823) <
      (25826919644 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (25826919644 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y3YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (-4) (-1) (62685254873171903555329 / 62500000000000000000000) (-146429893823 / 322379893823) : ℚ) : ℝ) <
      (25826919644 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y3YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y3 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y3YV11_arg_eq :
    barrierCase2Y3YV11LogArg = barrierComplex (496 / 15625) (-150951842619 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y3YV11LogArg, Case2PointData.Y3, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y3YV11_arg_regular :
    (barrierCase2Y3YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y3YV11LogArg).re := by
  rw [barrierCase2Y3YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y3YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y3YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y3YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-5) (-2) (23180084390071344779161 / 12207031250000000000000) (19840000000 / 150951842619) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y3YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y3YV11LogArg (-5) (-2) (23180084390071344779161 / 12207031250000000000000) (150951842619 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (150951842619 / 312500000000) : ℚ) = (19840000000 / 150951842619) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y3YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y3YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-5) (-2) (23180084390071344779161 / 12207031250000000000000) (19840000000 / 150951842619) <
      (-141854215400 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y3YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-141854215400 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y3YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y3YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (-5) (-2) (23180084390071344779161 / 12207031250000000000000) (19840000000 / 150951842619) : ℚ) : ℝ) <
      (-141854215400 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y3_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y3 : ℝ))).sum <
      (-1003038471135 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y3 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y3 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y3YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y3YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y3YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y3YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y3YV0_log_upper,
    barrierCase2Y3YV1_log_upper,
    barrierCase2Y3YV2_log_upper,
    barrierCase2Y3YV3_log_upper,
    barrierCase2Y3YV4_log_upper,
    barrierCase2Y3YV5_log_upper,
    barrierCase2Y3YV7_log_upper,
    barrierCase2Y3YV9_log_upper,
    barrierCase2Y3YV11_log_upper]

private theorem barrierCase2Y3_approx_upper :
    barrierCase2YApproxRat Y3 (-4) (-1) (1227250753 / 625000000) (8772749247 / 5000000000) + (-1003038471135 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y3_lt : barrierCase2Y (Y3 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y3 : ℝ)| ≤ 1 := by norm_num [Y3]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y3 hx
    (-4) (-1) (1227250753 / 625000000) (8772749247 / 5000000000)
    Y3_normalizations.1 Y3_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y3 (-4) (-1) (1227250753 / 625000000) (8772749247 / 5000000000) : ℚ) : ℝ) +
      (-1003038471135 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y3_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y3_YV_tail_upper]

end InternalCatalan

end

end OAI
