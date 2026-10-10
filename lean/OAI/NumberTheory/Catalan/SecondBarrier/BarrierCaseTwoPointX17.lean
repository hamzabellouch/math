import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX17Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X17XV0LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X17XV0_arg_eq :
    barrierCase2X17XV0LogArg = barrierComplex (22209786219 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV0LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV0_arg_regular :
    (barrierCase2X17XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV0LogArg).re := by
  rw [barrierCase2X17XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X17XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (493274603893682315961 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X17XV0LogArg (1) (0) (493274603893682315961 / 312500000000000000000) (22209786219 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (22209786219 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (493274603893682315961 / 312500000000000000000) (0 / 1) <
      (87365728748 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (87365728748 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X17XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (493274603893682315961 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (87365728748 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV1LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X17XV1_arg_eq :
    barrierCase2X17XV1LogArg = barrierComplex (60379358657 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV1LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV1_arg_regular :
    (barrierCase2X17XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV1LogArg).re := by
  rw [barrierCase2X17XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X17XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (3645666951830640843649 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X17XV1LogArg (1) (0) (3645666951830640843649 / 1953125000000000000000) (60379358657 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (60379358657 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (3645666951830640843649 / 1953125000000000000000) (0 / 1) <
      (29319889116 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (29319889116 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X17XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (3645666951830640843649 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (29319889116 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV2LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X17XV2_arg_eq :
    barrierCase2X17XV2LogArg = barrierComplex (18192351591 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV2LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV2_arg_regular :
    (barrierCase2X17XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV2LogArg).re := by
  rw [barrierCase2X17XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X17XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-6) (0) (330961656410560231281 / 244140625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X17XV2LogArg (-6) (0) (330961656410560231281 / 244140625000000000000) (18192351591 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (18192351591 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-6) (0) (330961656410560231281 / 244140625000000000000) (0 / 1) <
      (-49057773160 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-49057773160 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X17XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-6) (0) (330961656410560231281 / 244140625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-49057773160 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV3LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X17XV3_arg_eq :
    barrierCase2X17XV3LogArg = barrierComplex (15514061839 / 200000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV3LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV3_arg_regular :
    (barrierCase2X17XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV3LogArg).re := by
  rw [barrierCase2X17XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X17XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-8) (0) (240686114744316061921 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X17XV3LogArg (-8) (0) (240686114744316061921 / 156250000000000000000) (15514061839 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (15514061839 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-8) (0) (240686114744316061921 / 156250000000000000000) (0 / 1) <
      (126106267616 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (126106267616 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X17XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-8) (0) (240686114744316061921 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (126106267616 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV4LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X17XV4_arg_eq :
    barrierCase2X17XV4LogArg = barrierComplex (55696295063 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV4LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV4_arg_regular :
    (barrierCase2X17XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV4LogArg).re := by
  rw [barrierCase2X17XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X17XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-9) (0) (3102077283744758173969 / 3051757812500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X17XV4LogArg (-9) (0) (3102077283744758173969 / 3051757812500000000000) (55696295063 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (55696295063 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-9) (0) (3102077283744758173969 / 3051757812500000000000) (0 / 1) <
      (-361439144956 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-361439144956 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X17XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-9) (0) (3102077283744758173969 / 3051757812500000000000) (0 / 1) : ℚ) : ℝ) <
      (-361439144956 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV5LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X17XV5_arg_eq :
    barrierCase2X17XV5LogArg = barrierComplex (1 / 1) (-378681662541 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV5LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV5_arg_regular :
    (barrierCase2X17XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV5LogArg).re := by
  rw [barrierCase2X17XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X17XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (393399801544815802576681 / 250000000000000000000000) (121318337459 / 878681662541) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X17XV5LogArg (0) (-1) (393399801544815802576681 / 250000000000000000000000) (878681662541 / 500000000000) (121318337459 / 500000000000)
  have hratio : ((121318337459 / 500000000000) / (878681662541 / 500000000000) : ℚ) = (121318337459 / 878681662541) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (393399801544815802576681 / 250000000000000000000000) (121318337459 / 878681662541) <
      (155481916694 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (155481916694 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X17XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (393399801544815802576681 / 250000000000000000000000) (121318337459 / 878681662541) : ℚ) : ℝ) <
      (155481916694 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV7LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X17XV7_arg_eq :
    barrierCase2X17XV7LogArg = barrierComplex (1 / 1) (-87388075971 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV7LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV7_arg_regular :
    (barrierCase2X17XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV7LogArg).re := by
  rw [barrierCase2X17XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X17XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (17636675821913267592841 / 10000000000000000000000) (12611924029 / 187388075971) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X17XV7LogArg (0) (-1) (17636675821913267592841 / 10000000000000000000000) (187388075971 / 100000000000) (12611924029 / 100000000000)
  have hratio : ((12611924029 / 100000000000) / (187388075971 / 100000000000) : ℚ) = (12611924029 / 187388075971) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (17636675821913267592841 / 10000000000000000000000) (12611924029 / 187388075971) <
      (63950313168 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (63950313168 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X17XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (17636675821913267592841 / 10000000000000000000000) (12611924029 / 187388075971) : ℚ) : ℝ) <
      (63950313168 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV9LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X17XV9_arg_eq :
    barrierCase2X17XV9LogArg = barrierComplex (1 / 1) (-1854569167829 / 2000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV9LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV9_arg_regular :
    (barrierCase2X17XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV9LogArg).re := by
  rw [barrierCase2X17XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X17XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (7439426798261949568573241 / 4000000000000000000000000) (145430832171 / 3854569167829) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X17XV9LogArg (0) (-1) (7439426798261949568573241 / 4000000000000000000000000) (3854569167829 / 2000000000000) (145430832171 / 2000000000000)
  have hratio : ((145430832171 / 2000000000000) / (3854569167829 / 2000000000000) : ℚ) = (145430832171 / 3854569167829) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (7439426798261949568573241 / 4000000000000000000000000) (145430832171 / 3854569167829) <
      (-54916510304 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-54916510304 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X17XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (7439426798261949568573241 / 4000000000000000000000000) (145430832171 / 3854569167829) : ℚ) : ℝ) <
      (-54916510304 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XV11LogArg : ℂ :=
  1 - ((Case2PointData.X17 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X17XV11_arg_eq :
    barrierCase2X17XV11LogArg = barrierComplex (1 / 1) (-1194303704937 / 1250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XV11LogArg, Case2PointData.X17, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XV11_arg_regular :
    (barrierCase2X17XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XV11LogArg).re := by
  rw [barrierCase2X17XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X17XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2988861339626244758173969 / 1562500000000000000000000) (55696295063 / 2444303704937) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X17XV11LogArg (0) (-1) (2988861339626244758173969 / 1562500000000000000000000) (2444303704937 / 1250000000000) (55696295063 / 1250000000000)
  have hratio : ((55696295063 / 1250000000000) / (2444303704937 / 1250000000000) : ℚ) = (55696295063 / 2444303704937) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2988861339626244758173969 / 1562500000000000000000000) (55696295063 / 2444303704937) <
      (86136819199 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (86136819199 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X17XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2988861339626244758173969 / 1562500000000000000000000) (55696295063 / 2444303704937) : ℚ) : ℝ) <
      (86136819199 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X17_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X17 : ℝ))).sum <
      (623522914521 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X17 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X17 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X17XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X17XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X17XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X17XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X17XP0_log_upper,
    barrierCase2X17XP1_log_upper,
    barrierCase2X17XP2_log_upper,
    barrierCase2X17XP4_log_upper,
    barrierCase2X17XP6_log_upper,
    barrierCase2X17XP8_log_upper]

private theorem barrierCase2X17_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X17 : ℝ))).sum <
      (333600044878 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X17 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X17 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X17XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X17XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X17XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X17XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X17XV0_log_upper,
    barrierCase2X17XV1_log_upper,
    barrierCase2X17XV2_log_upper,
    barrierCase2X17XV3_log_upper,
    barrierCase2X17XV4_log_upper,
    barrierCase2X17XV5_log_upper,
    barrierCase2X17XV7_log_upper,
    barrierCase2X17XV9_log_upper,
    barrierCase2X17XV11_log_upper]

private theorem barrierCase2X17_approx_upper :
    barrierCase2XApproxRat X17 (-1) (-6) (0) (9709786219 / 5000000000) (290213781 / 156250000) (194279948418682315961 / 100000000000000000000) + (623522914521 / 1000000000000) + (333600044878 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X17_lt : barrierCase2X (X17 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X17 : ℝ)| ≤ 1 := by norm_num [X17]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X17 hx
    (-1) (-6) (0) (9709786219 / 5000000000) (290213781 / 156250000) (194279948418682315961 / 100000000000000000000)
    X17_normalizations.1 X17_normalizations.2.1 X17_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X17 (-1) (-6) (0) (9709786219 / 5000000000) (290213781 / 156250000) (194279948418682315961 / 100000000000000000000) : ℚ) : ℝ) +
      (623522914521 / 1000000000000) + (333600044878 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X17_XP_tail_upper, barrierCase2X17_XV_tail_upper]

end InternalCatalan

end

end OAI
