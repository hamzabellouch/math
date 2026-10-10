import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX6Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X6XV0LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X6XV0_arg_eq :
    barrierCase2X6XV0LogArg = barrierComplex (4695596677 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV0LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV0_arg_regular :
    (barrierCase2X6XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV0LogArg).re := by
  rw [barrierCase2X6XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X6XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-1) (0) (22048628153053442329 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X6XV0LogArg (-1) (0) (22048628153053442329 / 19531250000000000000) (4695596677 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (4695596677 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-1) (0) (22048628153053442329 / 19531250000000000000) (0 / 1) <
      (-43463097058 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-43463097058 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X6XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-1) (0) (22048628153053442329 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-43463097058 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV1LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X6XV1_arg_eq :
    barrierCase2X6XV1LogArg = barrierComplex (10961790031 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV1LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV1_arg_regular :
    (barrierCase2X6XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV1LogArg).re := by
  rw [barrierCase2X6XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X6XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (120160840683730980961 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X6XV1LogArg (-2) (0) (120160840683730980961 / 61035156250000000000) (10961790031 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (10961790031 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (120160840683730980961 / 61035156250000000000) (0 / 1) <
      (-15779209920 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-15779209920 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X6XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (120160840683730980961 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (-15779209920 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV2LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X6XV2_arg_eq :
    barrierCase2X6XV2LogArg = barrierComplex (79598436553 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV2LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV2_arg_regular :
    (barrierCase2X6XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV2LogArg).re := by
  rw [barrierCase2X6XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X6XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (6335911101681966521809 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X6XV2LogArg (0) (0) (6335911101681966521809 / 3906250000000000000000) (79598436553 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (79598436553 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (6335911101681966521809 / 3906250000000000000000) (0 / 1) <
      (6155482395 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (6155482395 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X6XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (6335911101681966521809 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (6155482395 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV3LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X6XV3_arg_eq :
    barrierCase2X6XV3LogArg = barrierComplex (129533663137 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV3LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV3_arg_regular :
    (barrierCase2X6XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV3LogArg).re := by
  rw [barrierCase2X6XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X6XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (16778969885689792680769 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X6XV3LogArg (0) (0) (16778969885689792680769 / 10000000000000000000000) (129533663137 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (129533663137 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (16778969885689792680769 / 10000000000000000000000) (0 / 1) <
      (-12764207009 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-12764207009 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X6XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (16778969885689792680769 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-12764207009 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV4LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X6XV4_arg_eq :
    barrierCase2X6XV4LogArg = barrierComplex (816191608729 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV4LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV4_arg_regular :
    (barrierCase2X6XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV4LogArg).re := by
  rw [barrierCase2X6XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X6XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (666168742159633028995441 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X6XV4LogArg (0) (0) (666168742159633028995441 / 390625000000000000000000) (816191608729 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (816191608729 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (666168742159633028995441 / 390625000000000000000000) (0 / 1) <
      (31008569684 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (31008569684 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X6XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (666168742159633028995441 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (31008569684 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV5LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X6XV5_arg_eq :
    barrierCase2X6XV5LogArg = barrierComplex (1 / 1) (60621729597 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV5LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV5_arg_regular :
    (barrierCase2X6XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV5LogArg).re := by
  rw [barrierCase2X6XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X6XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (66174994099331785782409 / 62500000000000000000000) (60621729597 / 250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X6XV5LogArg (0) (0) (66174994099331785782409 / 62500000000000000000000) (1 / 1) (60621729597 / 250000000000)
  have hratio : ((60621729597 / 250000000000) / (1 / 1) : ℚ) = (60621729597 / 250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (66174994099331785782409 / 62500000000000000000000) (60621729597 / 250000000000) <
      (-41842097564 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-41842097564 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X6XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (66174994099331785782409 / 62500000000000000000000) (60621729597 / 250000000000) : ℚ) : ℝ) <
      (-41842097564 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2X6XV7LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X6XV7_arg_eq :
    barrierCase2X6XV7LogArg = barrierComplex (1 / 1) (13989629907 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV7LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV7_arg_regular :
    (barrierCase2X6XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV7LogArg).re := by
  rw [barrierCase2X6XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X6XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2695709744934828828649 / 2500000000000000000000) (13989629907 / 50000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X6XV7LogArg (0) (0) (2695709744934828828649 / 2500000000000000000000) (1 / 1) (13989629907 / 50000000000)
  have hratio : ((13989629907 / 50000000000) / (1 / 1) : ℚ) = (13989629907 / 50000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2695709744934828828649 / 2500000000000000000000) (13989629907 / 50000000000) <
      (-47085480876 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-47085480876 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X6XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2695709744934828828649 / 2500000000000000000000) (13989629907 / 50000000000) : ℚ) : ℝ) <
      (-47085480876 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV9LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X6XV9_arg_eq :
    barrierCase2X6XV9LogArg = barrierComplex (1 / 1) (296891034693 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV9LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV9_arg_regular :
    (barrierCase2X6XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV9LogArg).re := by
  rw [barrierCase2X6XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X6XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1088144286481080129604249 / 1000000000000000000000000) (296891034693 / 1000000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X6XV9LogArg (0) (0) (1088144286481080129604249 / 1000000000000000000000000) (1 / 1) (296891034693 / 1000000000000)
  have hratio : ((296891034693 / 1000000000000) / (1 / 1) : ℚ) = (296891034693 / 1000000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1088144286481080129604249 / 1000000000000000000000000) (296891034693 / 1000000000000) <
      (15775935887 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (15775935887 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X6XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1088144286481080129604249 / 1000000000000000000000000) (296891034693 / 1000000000000) : ℚ) : ℝ) <
      (15775935887 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XV11LogArg : ℂ :=
  1 - ((Case2PointData.X6 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X6XV11_arg_eq :
    barrierCase2X6XV11LogArg = barrierComplex (1 / 1) (191191608729 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XV11LogArg, Case2PointData.X6, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XV11_arg_regular :
    (barrierCase2X6XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XV11LogArg).re := by
  rw [barrierCase2X6XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X6XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (427179231248383028995441 / 390625000000000000000000) (191191608729 / 625000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X6XV11LogArg (0) (0) (427179231248383028995441 / 390625000000000000000000) (1 / 1) (191191608729 / 625000000000)
  have hratio : ((191191608729 / 625000000000) / (1 / 1) : ℚ) = (191191608729 / 625000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (427179231248383028995441 / 390625000000000000000000) (191191608729 / 625000000000) <
      (-31773949352 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-31773949352 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X6XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (427179231248383028995441 / 390625000000000000000000) (191191608729 / 625000000000) : ℚ) : ℝ) <
      (-31773949352 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2X6_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X6 : ℝ))).sum <
      (75472192665 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X6 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X6 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X6XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X6XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X6XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X6XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X6XP0_log_upper,
    barrierCase2X6XP1_log_upper,
    barrierCase2X6XP2_log_upper,
    barrierCase2X6XP4_log_upper,
    barrierCase2X6XP6_log_upper,
    barrierCase2X6XP8_log_upper]

private theorem barrierCase2X6_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X6 : ℝ))).sum <
      (-244693645718 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X6 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X6 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X6XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X6XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X6XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X6XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X6XV0_log_upper,
    barrierCase2X6XV1_log_upper,
    barrierCase2X6XV2_log_upper,
    barrierCase2X6XV3_log_upper,
    barrierCase2X6XV4_log_upper,
    barrierCase2X6XV5_log_upper,
    barrierCase2X6XV7_log_upper,
    barrierCase2X6XV9_log_upper,
    barrierCase2X6XV11_log_upper]

private theorem barrierCase2X6_approx_upper :
    barrierCase2XApproxRat X6 (-2) (0) (0) (1554403323 / 1250000000) (6554403323 / 5000000000) (27416169690553442329 / 25000000000000000000) + (75472192665 / 1000000000000) + (-244693645718 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X6_lt : barrierCase2X (X6 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X6 : ℝ)| ≤ 1 := by norm_num [X6]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X6 hx
    (-2) (0) (0) (1554403323 / 1250000000) (6554403323 / 5000000000) (27416169690553442329 / 25000000000000000000)
    X6_normalizations.1 X6_normalizations.2.1 X6_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X6 (-2) (0) (0) (1554403323 / 1250000000) (6554403323 / 5000000000) (27416169690553442329 / 25000000000000000000) : ℚ) : ℝ) +
      (75472192665 / 1000000000000) + (-244693645718 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X6_XP_tail_upper, barrierCase2X6_XV_tail_upper]

end InternalCatalan

end

end OAI
