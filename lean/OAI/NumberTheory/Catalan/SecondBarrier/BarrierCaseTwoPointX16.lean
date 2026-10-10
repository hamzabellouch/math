import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX16Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X16XV0LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X16XV0_arg_eq :
    barrierCase2X16XV0LogArg = barrierComplex (5458153641 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV0LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV0_arg_regular :
    (barrierCase2X16XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV0LogArg).re := by
  rw [barrierCase2X16XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X16XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (29791441168761556881 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X16XV0LogArg (1) (0) (29791441168761556881 / 19531250000000000000) (5458153641 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5458153641 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (29791441168761556881 / 19531250000000000000) (0 / 1) <
      (84762395771 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (84762395771 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X16XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (29791441168761556881 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (84762395771 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV1LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X16XV1_arg_eq :
    barrierCase2X16XV1LogArg = barrierComplex (14811960923 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV1LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV1_arg_regular :
    (barrierCase2X16XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV1LogArg).re := by
  rw [barrierCase2X16XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X16XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (219394186384479011929 / 122070312500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X16XV1LogArg (1) (0) (219394186384479011929 / 122070312500000000000) (14811960923 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (14811960923 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (219394186384479011929 / 122070312500000000000) (0 / 1) <
      (28477727417 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (28477727417 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X16XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (219394186384479011929 / 122070312500000000000) (0 / 1) : ℚ) : ℝ) <
      (28477727417 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV2LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X16XV2_arg_eq :
    barrierCase2X16XV2LogArg = barrierComplex (5585309949 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV2LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV2_arg_regular :
    (barrierCase2X16XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV2LogArg).re := by
  rw [barrierCase2X16XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X16XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-5) (0) (31195687226398382601 / 30517578125000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X16XV2LogArg (-5) (0) (31195687226398382601 / 30517578125000000000) (5585309949 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (5585309949 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-5) (0) (31195687226398382601 / 30517578125000000000) (0 / 1) <
      (-43828685043 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-43828685043 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X16XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-5) (0) (31195687226398382601 / 30517578125000000000) (0 / 1) : ℚ) : ℝ) <
      (-43828685043 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV3LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X16XV3_arg_eq :
    barrierCase2X16XV3LogArg = barrierComplex (5670080821 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV3LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV3_arg_regular :
    (barrierCase2X16XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV3LogArg).re := by
  rw [barrierCase2X16XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X16XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-7) (0) (32149816516672034041 / 19531250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X16XV3LogArg (-7) (0) (32149816516672034041 / 19531250000000000000) (5670080821 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (5670080821 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-7) (0) (32149816516672034041 / 19531250000000000000) (0 / 1) <
      (107374545369 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (107374545369 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X16XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-7) (0) (32149816516672034041 / 19531250000000000000) (0 / 1) : ℚ) : ℝ) <
      (107374545369 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV4LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X16XV4_arg_eq :
    barrierCase2X16XV4LogArg = barrierComplex (25522102157 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV4LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV4_arg_regular :
    (barrierCase2X16XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV4LogArg).re := by
  rw [barrierCase2X16XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X16XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-8) (0) (651377698512344052649 / 381469726562500000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X16XV4LogArg (-8) (0) (651377698512344052649 / 381469726562500000000) (25522102157 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (25522102157 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-8) (0) (651377698512344052649 / 381469726562500000000) (0 / 1) <
      (-291041762053 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-291041762053 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X16XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-8) (0) (651377698512344052649 / 381469726562500000000) (0 / 1) : ℚ) : ℝ) <
      (-291041762053 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV5LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X16XV5_arg_eq :
    barrierCase2X16XV5LogArg = barrierComplex (1 / 1) (-90992991999 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV5LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV5_arg_regular :
    (barrierCase2X16XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV5LogArg).re := by
  rw [barrierCase2X16XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X16XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (23904724592930078016001 / 15625000000000000000000) (34007008001 / 215992991999) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X16XV5LogArg (0) (-1) (23904724592930078016001 / 15625000000000000000000) (215992991999 / 125000000000) (34007008001 / 125000000000)
  have hratio : ((34007008001 / 125000000000) / (215992991999 / 125000000000) : ℚ) = (34007008001 / 215992991999) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (23904724592930078016001 / 15625000000000000000000) (34007008001 / 215992991999) <
      (149918984764 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (149918984764 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X16XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (23904724592930078016001 / 15625000000000000000000) (34007008001 / 215992991999) : ℚ) : ℝ) <
      (149918984764 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV7LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X16XV7_arg_eq :
    barrierCase2X16XV7LogArg = barrierComplex (1 / 1) (-20998382769 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV7LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV7_arg_regular :
    (barrierCase2X16XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV7LogArg).re := by
  rw [barrierCase2X16XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X16XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (1065932078913436107361 / 625000000000000000000) (4001617231 / 45998382769) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X16XV7LogArg (0) (-1) (1065932078913436107361 / 625000000000000000000) (45998382769 / 25000000000) (4001617231 / 25000000000)
  have hratio : ((4001617231 / 25000000000) / (45998382769 / 25000000000) : ℚ) = (4001617231 / 45998382769) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (1065932078913436107361 / 625000000000000000000) (4001617231 / 45998382769) <
      (63623886691 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (63623886691 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X16XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (1065932078913436107361 / 625000000000000000000) (4001617231 / 45998382769) : ℚ) : ℝ) <
      (63623886691 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV9LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X16XV9_arg_eq :
    barrierCase2X16XV9LogArg = barrierComplex (1 / 1) (-445632345431 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV9LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV9_arg_regular :
    (barrierCase2X16XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV9LogArg).re := by
  rw [barrierCase2X16XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X16XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (448588187294334106575761 / 250000000000000000000000) (54367654569 / 945632345431) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X16XV9LogArg (0) (-1) (448588187294334106575761 / 250000000000000000000000) (945632345431 / 500000000000) (54367654569 / 500000000000)
  have hratio : ((54367654569 / 500000000000) / (945632345431 / 500000000000) : ℚ) = (54367654569 / 945632345431) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (448588187294334106575761 / 250000000000000000000000) (54367654569 / 945632345431) <
      (-53142049652 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-53142049652 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X16XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (448588187294334106575761 / 250000000000000000000000) (54367654569 / 945632345431) : ℚ) : ℝ) <
      (-53142049652 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XV11LogArg : ℂ :=
  1 - ((Case2PointData.X16 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X16XV11_arg_eq :
    barrierCase2X16XV11LogArg = barrierComplex (1 / 1) (-286977897843 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XV11LogArg, Case2PointData.X16, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XV11_arg_regular :
    (barrierCase2X16XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XV11LogArg).re := by
  rw [barrierCase2X16XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X16XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (180012563850387344052649 / 97656250000000000000000) (25522102157 / 599477897843) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X16XV11LogArg (0) (-1) (180012563850387344052649 / 97656250000000000000000) (599477897843 / 312500000000) (25522102157 / 312500000000)
  have hratio : ((25522102157 / 312500000000) / (599477897843 / 312500000000) : ℚ) = (25522102157 / 599477897843) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (180012563850387344052649 / 97656250000000000000000) (25522102157 / 599477897843) <
      (83800371241 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (83800371241 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X16XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (180012563850387344052649 / 97656250000000000000000) (25522102157 / 599477897843) : ℚ) : ℝ) <
      (83800371241 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X16_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X16 : ℝ))).sum <
      (513913439712 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X16 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X16 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X16XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X16XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X16XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X16XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X16XP0_log_upper,
    barrierCase2X16XP1_log_upper,
    barrierCase2X16XP2_log_upper,
    barrierCase2X16XP4_log_upper,
    barrierCase2X16XP6_log_upper,
    barrierCase2X16XP8_log_upper]

private theorem barrierCase2X16_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X16 : ℝ))).sum <
      (374146607549 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X16 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X16 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X16XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X16XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X16XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X16XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X16XV0_log_upper,
    barrierCase2X16XV1_log_upper,
    barrierCase2X16XV2_log_upper,
    barrierCase2X16XV3_log_upper,
    barrierCase2X16XV4_log_upper,
    barrierCase2X16XV5_log_upper,
    barrierCase2X16XV7_log_upper,
    barrierCase2X16XV9_log_upper,
    barrierCase2X16XV11_log_upper]

private theorem barrierCase2X16_approx_upper :
    barrierCase2XApproxRat X16 (-1) (-4) (0) (2333153641 / 1250000000) (166846359 / 156250000) (11693605912511556881 / 6250000000000000000) + (513913439712 / 1000000000000) + (374146607549 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X16_lt : barrierCase2X (X16 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X16 : ℝ)| ≤ 1 := by norm_num [X16]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X16 hx
    (-1) (-4) (0) (2333153641 / 1250000000) (166846359 / 156250000) (11693605912511556881 / 6250000000000000000)
    X16_normalizations.1 X16_normalizations.2.1 X16_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X16 (-1) (-4) (0) (2333153641 / 1250000000) (166846359 / 156250000) (11693605912511556881 / 6250000000000000000) : ℚ) : ℝ) +
      (513913439712 / 1000000000000) + (374146607549 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X16_XP_tail_upper, barrierCase2X16_XV_tail_upper]

end InternalCatalan

end

end OAI
