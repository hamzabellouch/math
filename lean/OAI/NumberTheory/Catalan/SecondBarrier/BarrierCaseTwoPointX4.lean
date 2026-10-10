import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX4Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X4XV0LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X4XV0_arg_eq :
    barrierCase2X4XV0LogArg = barrierComplex (1462827187 / 2500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV0LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV0_arg_regular :
    (barrierCase2X4XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV0LogArg).re := by
  rw [barrierCase2X4XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X4XV0LogArg (-2) (0) (2139863379026332969 / 1562500000000000000) (1462827187 / 2500000000) (0 / 1)
  have hratio : ((0 / 1) / (1462827187 / 2500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1) <
      (-81455571945 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-81455571945 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1) : ℚ) : ℝ) <
      (-81455571945 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV1LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X4XV1_arg_eq :
    barrierCase2X4XV1LogArg = barrierComplex (3138481561 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV1LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV1_arg_regular :
    (barrierCase2X4XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV1LogArg).re := by
  rw [barrierCase2X4XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X4XV1LogArg (-2) (0) (9850066508736996721 / 9765625000000000000) (3138481561 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (3138481561 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1) <
      (-30664933583 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-30664933583 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-30664933583 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV2LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X4XV2_arg_eq :
    barrierCase2X4XV2LogArg = barrierComplex (36408900943 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV2LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV2_arg_regular :
    (barrierCase2X4XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV2LogArg).re := by
  rw [barrierCase2X4XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X4XV2LogArg (1) (0) (1325608067877186289249 / 1250000000000000000000) (36408900943 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (36408900943 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1) <
      (9569104368 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (9569104368 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (9569104368 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV3LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X4XV3_arg_eq :
    barrierCase2X4XV3LogArg = barrierComplex (59706283447 / 40000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV3LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV3_arg_regular :
    (barrierCase2X4XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV3LogArg).re := by
  rw [barrierCase2X4XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X4XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X4XV3LogArg (1) (0) (3564840283053506201809 / 3200000000000000000000) (59706283447 / 40000000000) (0 / 1)
  have hratio : ((0 / 1) / (59706283447 / 40000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1) <
      (-19758050779 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-19758050779 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X4XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-19758050779 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV4LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X4XV4_arg_eq :
    barrierCase2X4XV4LogArg = barrierComplex (377572255999 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV4LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV4_arg_regular :
    (barrierCase2X4XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV4LogArg).re := by
  rw [barrierCase2X4XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X4XV4LogArg (1) (0) (142560808500174391488001 / 125000000000000000000000) (377572255999 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (377572255999 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1) <
      (47901782040 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (47901782040 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (47901782040 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV5LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X4XV5_arg_eq :
    barrierCase2X4XV5LogArg = barrierComplex (1 / 1) (40449739707 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV5LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV5_arg_regular :
    (barrierCase2X4XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV5LogArg).re := by
  rw [barrierCase2X4XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X4XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X4XV5LogArg (0) (0) (11636181442364052445849 / 10000000000000000000000) (1 / 1) (40449739707 / 100000000000)
  have hratio : ((40449739707 / 100000000000) / (1 / 1) : ℚ) = (40449739707 / 100000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000) <
      (-63573597776 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-63573597776 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X4XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000) : ℚ) : ℝ) <
      (-63573597776 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV7LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X4XV7_arg_eq :
    barrierCase2X4XV7LogArg = barrierComplex (1 / 1) (9334555317 / 20000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV7LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV7_arg_regular :
    (barrierCase2X4XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV7LogArg).re := by
  rw [barrierCase2X4XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X4XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X4XV7LogArg (0) (0) (487133922966132970489 / 400000000000000000000) (1 / 1) (9334555317 / 20000000000)
  have hratio : ((9334555317 / 20000000000) / (1 / 1) : ℚ) = (9334555317 / 20000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000) <
      (-81355116341 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-81355116341 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X4XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000) : ℚ) : ℝ) <
      (-81355116341 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV9LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X4XV9_arg_eq :
    barrierCase2X4XV9LogArg = barrierComplex (1 / 1) (198100007283 / 400000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV9LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV9_arg_regular :
    (barrierCase2X4XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV9LogArg).re := by
  rw [barrierCase2X4XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X4XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X4XV9LogArg (0) (0) (199243612885524653042089 / 160000000000000000000000) (1 / 1) (198100007283 / 400000000000)
  have hratio : ((198100007283 / 400000000000) / (1 / 1) : ℚ) = (198100007283 / 400000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000) <
      (23718033220 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (23718033220 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X4XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000) : ℚ) : ℝ) <
      (23718033220 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XV11LogArg : ℂ :=
  1 - ((Case2PointData.X4 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X4XV11_arg_eq :
    barrierCase2X4XV11LogArg = barrierComplex (1 / 1) (127572255999 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XV11LogArg, Case2PointData.X4, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XV11_arg_regular :
    (barrierCase2X4XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XV11LogArg).re := by
  rw [barrierCase2X4XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X4XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X4XV11LogArg (0) (1) (78774680500674391488001 / 62500000000000000000000) (377572255999 / 250000000000) (-122427744001 / 250000000000)
  have hratio : ((-122427744001 / 250000000000) / (377572255999 / 250000000000) : ℚ) = (-122427744001 / 377572255999) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999) <
      (-50043494195 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-50043494195 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X4XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999) : ℚ) : ℝ) <
      (-50043494195 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X4_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X4 : ℝ))).sum <
      (-551935825239 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X4 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X4 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X4XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X4XP0_log_upper,
    barrierCase2X4XP1_log_upper,
    barrierCase2X4XP2_log_upper,
    barrierCase2X4XP4_log_upper,
    barrierCase2X4XP6_log_upper,
    barrierCase2X4XP8_log_upper]

private theorem barrierCase2X4_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X4 : ℝ))).sum <
      (-416916020083 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X4 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X4 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X4XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X4XV0_log_upper,
    barrierCase2X4XV1_log_upper,
    barrierCase2X4XV2_log_upper,
    barrierCase2X4XV3_log_upper,
    barrierCase2X4XV4_log_upper,
    barrierCase2X4XV5_log_upper,
    barrierCase2X4XV7_log_upper,
    barrierCase2X4XV9_log_upper,
    barrierCase2X4XV11_log_upper]

private theorem barrierCase2X4_approx_upper :
    barrierCase2XApproxRat X4 (-1) (0) (0) (1037172813 / 1000000000) (3037172813 / 2000000000) (5075727444026332969 / 4000000000000000000) + (-551935825239 / 1000000000000) + (-416916020083 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X4_lt : barrierCase2X (X4 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X4 : ℝ)| ≤ 1 := by norm_num [X4]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X4 hx
    (-1) (0) (0) (1037172813 / 1000000000) (3037172813 / 2000000000) (5075727444026332969 / 4000000000000000000)
    X4_normalizations.1 X4_normalizations.2.1 X4_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X4 (-1) (0) (0) (1037172813 / 1000000000) (3037172813 / 2000000000) (5075727444026332969 / 4000000000000000000) : ℚ) : ℝ) +
      (-551935825239 / 1000000000000) + (-416916020083 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X4_XP_tail_upper, barrierCase2X4_XV_tail_upper]

end InternalCatalan

end

end OAI
