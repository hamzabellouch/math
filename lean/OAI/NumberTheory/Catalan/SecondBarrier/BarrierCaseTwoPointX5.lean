import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX5Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X5XV0LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X5XV0_arg_eq :
    barrierCase2X5XV0LogArg = barrierComplex (4242182921 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV0LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV0_arg_regular :
    (barrierCase2X5XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV0LogArg).re := by
  rw [barrierCase2X5XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X5XV0LogArg (-2) (0) (17996115935224092241 / 9765625000000000000) (4242182921 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (4242182921 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1) <
      (-58897472640 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-58897472640 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (17996115935224092241 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-58897472640 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV1LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X5XV1_arg_eq :
    barrierCase2X5XV1LogArg = barrierComplex (9601548763 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV1LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV1_arg_regular :
    (barrierCase2X5XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV1LogArg).re := by
  rw [barrierCase2X5XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X5XV1LogArg (-2) (0) (92189738648266830169 / 61035156250000000000) (9601548763 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (9601548763 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1) <
      (-21677269311 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-21677269311 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (92189738648266830169 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-21677269311 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV2LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X5XV2_arg_eq :
    barrierCase2X5XV2LogArg = barrierComplex (84585987869 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV2LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV2_arg_regular :
    (barrierCase2X5XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV2LogArg).re := by
  rw [barrierCase2X5XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X5XV2LogArg (0) (0) (7154789343774615161161 / 3906250000000000000000) (84585987869 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (84585987869 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1) <
      (7702426992 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (7702426992 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (7154789343774615161161 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (7702426992 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV3LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X5XV3_arg_eq :
    barrierCase2X5XV3LogArg = barrierComplex (138148524501 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV3LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV3_arg_regular :
    (barrierCase2X5XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV3LogArg).re := by
  rw [barrierCase2X5XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X5XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X5XV3LogArg (0) (0) (19085014821803397299001 / 10000000000000000000000) (138148524501 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (138148524501 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1) <
      (-15940259828 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-15940259828 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X5XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-15940259828 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV4LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X5XV4_arg_eq :
    barrierCase2X5XV4LogArg = barrierComplex (871961500717 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV4LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV4_arg_regular :
    (barrierCase2X5XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV4LogArg).re := by
  rw [barrierCase2X5XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X5XV4LogArg (0) (0) (760316858732642791514089 / 390625000000000000000000) (871961500717 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (871961500717 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1) <
      (38687721880 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (38687721880 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (38687721880 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV5LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X5XV5_arg_eq :
    barrierCase2X5XV5LogArg = barrierComplex (1 / 1) (78304866081 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV5LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV5_arg_regular :
    (barrierCase2X5XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV5LogArg).re := by
  rw [barrierCase2X5XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X5XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X5XV5LogArg (0) (0) (68631652051963344298561 / 62500000000000000000000) (1 / 1) (78304866081 / 250000000000)
  have hratio : ((78304866081 / 250000000000) / (1 / 1) : ℚ) = (78304866081 / 250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000) <
      (-51979476494 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-51979476494 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X5XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000) : ℚ) : ℝ) <
      (-51979476494 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV7LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X5XV7_arg_eq :
    barrierCase2X5XV7LogArg = barrierComplex (1 / 1) (18070353711 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV7LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV7_arg_regular :
    (barrierCase2X5XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV7LogArg).re := by
  rw [barrierCase2X5XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X5XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X5XV7LogArg (0) (0) (2826537683240651471521 / 2500000000000000000000) (1 / 1) (18070353711 / 50000000000)
  have hratio : ((18070353711 / 50000000000) / (1 / 1) : ℚ) = (18070353711 / 50000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000) <
      (-61966174193 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-61966174193 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X5XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000) : ℚ) : ℝ) <
      (-61966174193 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV9LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X5XV9_arg_eq :
    barrierCase2X5XV9LogArg = barrierComplex (1 / 1) (383493062089 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV9LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV9_arg_regular :
    (barrierCase2X5XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV9LogArg).re := by
  rw [barrierCase2X5XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X5XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X5XV9LogArg (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (1 / 1) (383493062089 / 1000000000000)
  have hratio : ((383493062089 / 1000000000000) / (1 / 1) : ℚ) = (383493062089 / 1000000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000) <
      (19515063396 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (19515063396 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X5XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000) : ℚ) : ℝ) <
      (19515063396 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XV11LogArg : ℂ :=
  1 - ((Case2PointData.X5 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X5XV11_arg_eq :
    barrierCase2X5XV11LogArg = barrierComplex (1 / 1) (246961500717 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XV11LogArg, Case2PointData.X5, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XV11_arg_regular :
    (barrierCase2X5XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XV11LogArg).re := by
  rw [barrierCase2X5XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X5XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X5XV11LogArg (0) (0) (451614982836392791514089 / 390625000000000000000000) (1 / 1) (246961500717 / 625000000000)
  have hratio : ((246961500717 / 625000000000) / (1 / 1) : ℚ) = (246961500717 / 625000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000) <
      (-40113838448 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-40113838448 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X5XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000) : ℚ) : ℝ) <
      (-40113838448 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X5_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X5 : ℝ))).sum <
      (-217794806672 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X5 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X5 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X5XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X5XP0_log_upper,
    barrierCase2X5XP1_log_upper,
    barrierCase2X5XP2_log_upper,
    barrierCase2X5XP4_log_upper,
    barrierCase2X5XP6_log_upper,
    barrierCase2X5XP8_log_upper]

private theorem barrierCase2X5_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X5 : ℝ))).sum <
      (-319213704385 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X5 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X5 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X5XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X5XV0_log_upper,
    barrierCase2X5XV1_log_upper,
    barrierCase2X5XV2_log_upper,
    barrierCase2X5XV3_log_upper,
    barrierCase2X5XV4_log_upper,
    barrierCase2X5XV5_log_upper,
    barrierCase2X5XV7_log_upper,
    barrierCase2X5XV9_log_upper,
    barrierCase2X5XV11_log_upper]

private theorem barrierCase2X5_approx_upper :
    barrierCase2XApproxRat X5 (-2) (0) (0) (2007817079 / 1250000000) (7007817079 / 5000000000) (29031329422724092241 / 25000000000000000000) + (-217794806672 / 1000000000000) + (-319213704385 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X5_lt : barrierCase2X (X5 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X5 : ℝ)| ≤ 1 := by norm_num [X5]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X5 hx
    (-2) (0) (0) (2007817079 / 1250000000) (7007817079 / 5000000000) (29031329422724092241 / 25000000000000000000)
    X5_normalizations.1 X5_normalizations.2.1 X5_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X5 (-2) (0) (0) (2007817079 / 1250000000) (7007817079 / 5000000000) (29031329422724092241 / 25000000000000000000) : ℚ) : ℝ) +
      (-217794806672 / 1000000000000) + (-319213704385 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X5_XP_tail_upper, barrierCase2X5_XV_tail_upper]

end InternalCatalan

end

end OAI
