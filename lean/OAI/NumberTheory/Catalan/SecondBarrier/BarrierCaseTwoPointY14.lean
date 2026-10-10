import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2Y14YV0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1 + (barrierV2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV0_arg_eq :
    barrierCase2Y14YV0LogArg = barrierComplex (5060509299 / 1562500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV0LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV0_arg_regular :
    (barrierCase2Y14YV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV0LogArg).re := by
  rw [barrierCase2Y14YV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV0_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV0_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y14YV0LogArg).re -
      ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (25608754365265471401 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-15199211 / 100000000) (0 / 1)
    barrierCase2Y14YV0LogArg (3) (0) (25608754365265471401 / 19531250000000000000) (5060509299 / 1562500000) (0 / 1)
  have hratio : ((0 / 1) / (5060509299 / 1562500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV0_approx_upper :
    barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (25608754365265471401 / 19531250000000000000) (0 / 1) <
      (-178618092021 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV0_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-178618092021 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2Y14YV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV0_error).2
  have ha : ((barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (3) (0) (25608754365265471401 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-178618092021 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1 + (barrierV2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV1_arg_eq :
    barrierCase2Y14YV1LogArg = barrierComplex (15000277897 / 3906250000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV1LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV1_arg_regular :
    (barrierCase2Y14YV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV1LogArg).re := by
  rw [barrierCase2Y14YV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV1_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV1_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y14YV1LogArg).re -
      ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (225008336987226742609 / 122070312500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2225831 / 50000000) (0 / 1)
    barrierCase2Y14YV1LogArg (3) (0) (225008336987226742609 / 122070312500000000000) (15000277897 / 3906250000) (0 / 1)
  have hratio : ((0 / 1) / (15000277897 / 3906250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV1_approx_upper :
    barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (225008336987226742609 / 122070312500000000000) (0 / 1) <
      (-59896706791 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV1_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-59896706791 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2Y14YV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (225008336987226742609 / 122070312500000000000) (0 / 1) : ℚ) : ℝ) <
      (-59896706791 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1 + (barrierV2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV2_arg_eq :
    barrierCase2Y14YV2LogArg = barrierComplex (246897711 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV2LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV2_arg_regular :
    (barrierCase2Y14YV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV2LogArg).re := by
  rw [barrierCase2Y14YV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV2_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV2_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y14YV2LogArg).re -
      ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-12) (0) (60958479697039521 / 59604644775390625) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1272699 / 50000000) (0 / 1)
    barrierCase2Y14YV2LogArg (-12) (0) (60958479697039521 / 59604644775390625) (246897711 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (246897711 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV2_approx_upper :
    barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-12) (0) (60958479697039521 / 59604644775390625) (0 / 1) <
      (105574285400 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV2_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (105574285400 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2Y14YV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV2_error).2
  have ha : ((barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-12) (0) (60958479697039521 / 59604644775390625) (0 / 1) : ℚ) : ℝ) <
      (105574285400 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV3LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1 + (barrierV2Tail.getD 3 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV3_arg_eq :
    barrierCase2Y14YV3LogArg = barrierComplex (100323319 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV3LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV3_arg_regular :
    (barrierCase2Y14YV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV3LogArg).re := by
  rw [barrierCase2Y14YV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV3_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV3_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y14YV3LogArg).re -
      ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-16) (0) (10064768335175761 / 9536743164062500) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2466317 / 50000000) (0 / 1)
    barrierCase2Y14YV3LogArg (-16) (0) (10064768335175761 / 9536743164062500) (100323319 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (100323319 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV3_approx_upper :
    barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-16) (0) (10064768335175761 / 9536743164062500) (0 / 1) <
      (-272194234363 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV3_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-272194234363 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2Y14YV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV3_error).2
  have ha : ((barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-16) (0) (10064768335175761 / 9536743164062500) (0 / 1) : ℚ) : ℝ) <
      (-272194234363 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1 + (barrierV2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV4_arg_eq :
    barrierCase2Y14YV4LogArg = barrierComplex (284856223 / 156250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV4LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV4_arg_regular :
    (barrierCase2Y14YV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV4LogArg).re := by
  rw [barrierCase2Y14YV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV4_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV4_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y14YV4LogArg).re -
      ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-19) (0) (2596578169018423328 / 1490116119384765625) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-11618157 / 100000000) (0 / 1)
    barrierCase2Y14YV4LogArg (-19) (0) (2596578169018423328 / 1490116119384765625) (284856223 / 156250000000) (0 / 1)
  have hratio : ((0 / 1) / (284856223 / 156250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV4_approx_upper :
    barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-19) (0) (2596578169018423328 / 1490116119384765625) (0 / 1) <
      (732783650846 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV4_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (732783650846 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2Y14YV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV4_error).2
  have ha : ((barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-19) (0) (2596578169018423328 / 1490116119384765625) (0 / 1) : ℚ) : ℝ) <
      (732783650846 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV5LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1 + (barrierV2Tail.getD 5 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV5_arg_eq :
    barrierCase2Y14YV5LogArg = barrierComplex (979 / 2500) (-97422362661 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV5LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV5_arg_regular :
    (barrierCase2Y14YV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV5LogArg).re := by
  rw [barrierCase2Y14YV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV5_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV5_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y14YV5LogArg).re -
      ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (10090142371451407000921 / 7812500000000000000000) (24475000000 / 97422362661) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y14YV5LogArg (1) (-2) (10090142371451407000921 / 7812500000000000000000) (97422362661 / 31250000000) (979 / 1250)
  have hratio : ((979 / 1250) / (97422362661 / 31250000000) : ℚ) = (24475000000 / 97422362661) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV5_approx_upper :
    barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (10090142371451407000921 / 7812500000000000000000) (24475000000 / 97422362661) <
      (-319275624684 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV5_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-319275624684 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2Y14YV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV5_error).2
  have ha : ((barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (10090142371451407000921 / 7812500000000000000000) (24475000000 / 97422362661) : ℚ) : ℝ) <
      (-319275624684 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2Y14YV7LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1 + (barrierV2Tail.getD 7 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV7_arg_eq :
    barrierCase2Y14YV7LogArg = barrierComplex (19 / 100) (-22482083691 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV7LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV7_arg_regular :
    (barrierCase2Y14YV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV7LogArg).re := by
  rw [barrierCase2Y14YV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV7_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV7_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y14YV7LogArg).re -
      ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (511084712089128183481 / 312500000000000000000) (2375000000 / 22482083691) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y14YV7LogArg (1) (-2) (511084712089128183481 / 312500000000000000000) (22482083691 / 6250000000) (19 / 50)
  have hratio : ((19 / 50) / (22482083691 / 6250000000) : ℚ) = (2375000000 / 22482083691) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV7_approx_upper :
    barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (511084712089128183481 / 312500000000000000000) (2375000000 / 22482083691) <
      (-128361347705 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV7_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-128361347705 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2Y14YV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV7_error).2
  have ha : ((barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (511084712089128183481 / 312500000000000000000) (2375000000 / 22482083691) : ℚ) : ℝ) <
      (-128361347705 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV9LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1 + (barrierV2Tail.getD 9 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV9_arg_eq :
    barrierCase2Y14YV9LogArg = barrierComplex (3519 / 40000) (-477119776109 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV9LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV9_arg_regular :
    (barrierCase2Y14YV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV9LogArg).re := by
  rw [barrierCase2Y14YV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV9_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV9_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y14YV9LogArg).re -
      ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (228127005793364787179881 / 125000000000000000000000) (21993750000 / 477119776109) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y14YV9LogArg (1) (-2) (228127005793364787179881 / 125000000000000000000000) (477119776109 / 125000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (477119776109 / 125000000000) : ℚ) = (21993750000 / 477119776109) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV9_approx_upper :
    barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (228127005793364787179881 / 125000000000000000000000) (21993750000 / 477119776109) <
      (112480899376 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV9_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (112480899376 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2Y14YV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV9_error).2
  have ha : ((barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (228127005793364787179881 / 125000000000000000000000) (21993750000 / 477119776109) : ℚ) : ℝ) <
      (112480899376 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2Y14YV11LogArg : ℂ :=
  1 - 2 * ((Case2PointData.Y14 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1 + (barrierV2Tail.getD 11 (0, 0)).1 ^ 2

private theorem barrierCase2Y14YV11_arg_eq :
    barrierCase2Y14YV11LogArg = barrierComplex (496 / 15625) (-307255143777 / 156250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2Y14YV11LogArg, Case2PointData.Y14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2Y14YV11_arg_regular :
    (barrierCase2Y14YV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2Y14YV11LogArg).re := by
  rw [barrierCase2Y14YV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2Y14YV11_weight_eq :
    (-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2Y14YV11_error :
    |((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y14YV11LogArg).re -
      ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (94430324977424941825729 / 48828125000000000000000) (4960000000 / 307255143777) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2Y14YV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y14YV11LogArg (1) (-2) (94430324977424941825729 / 48828125000000000000000) (307255143777 / 78125000000) (992 / 15625)
  have hratio : ((992 / 15625) / (307255143777 / 78125000000) : ℚ) = (4960000000 / 307255143777) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2Y14YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2Y14YV11_approx_upper :
    barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (94430324977424941825729 / 48828125000000000000000) (4960000000 / 307255143777) <
      (-175753475467 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2Y14YV11_log_upper :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-175753475467 / 1000000000000 : ℝ) := by
  change ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2Y14YV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2Y14YV11_error).2
  have ha : ((barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (94430324977424941825729 / 48828125000000000000000) (4960000000 / 307255143777) : ℚ) : ℝ) <
      (-175753475467 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14YV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2Y14_YV_tail_upper :
    (barrierV2Tail.map (barrierCase2YVLogTerm (Y14 : ℝ))).sum <
      (-694170193889 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2YVLogTerm (Y14 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2YVLogTerm (Y14 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y14YV5_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y14YV7_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y14YV9_arg_regular
    · exact barrierCase2YVLogTerm_conj _ _ _ barrierCase2Y14YV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2Y14YV0_log_upper,
    barrierCase2Y14YV1_log_upper,
    barrierCase2Y14YV2_log_upper,
    barrierCase2Y14YV3_log_upper,
    barrierCase2Y14YV4_log_upper,
    barrierCase2Y14YV5_log_upper,
    barrierCase2Y14YV7_log_upper,
    barrierCase2Y14YV9_log_upper,
    barrierCase2Y14YV11_log_upper]

private theorem barrierCase2Y14_approx_upper :
    barrierCase2YApproxRat Y14 (-1) (-11) (2498009299 / 1250000000) (15925608 / 9765625) + (-694170193889 / 1000000000000) <
      (-160890 / 100000 - 1 / 1000000000000000 : ℚ) := by
  unfold barrierCase2YApproxRat barrierCase2YRat
  rw [barrierCase2TV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2Y14_lt : barrierCase2Y (Y14 : ℝ) < (-160890 / 100000 : ℝ) := by
  have hx : |(Y14 : ℝ)| ≤ 1 := by norm_num [Y14]
  have he := (abs_lt.mp (barrierCase2Y_realLog_approx_error Y14 hx
    (-1) (-11) (2498009299 / 1250000000) (15925608 / 9765625)
    Y14_normalizations.1 Y14_normalizations.2)).2
  have ha : ((barrierCase2YApproxRat Y14 (-1) (-11) (2498009299 / 1250000000) (15925608 / 9765625) : ℚ) : ℝ) +
      (-694170193889 / 1000000000000) < (-160890 / 100000 - 1 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2Y14_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2Y14_YV_tail_upper]

end InternalCatalan

end

end OAI
