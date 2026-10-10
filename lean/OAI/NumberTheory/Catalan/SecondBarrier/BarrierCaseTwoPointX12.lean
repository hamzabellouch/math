import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX12Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X12XV0LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X12XV0_arg_eq :
    barrierCase2X12XV0LogArg = barrierComplex (16881119427 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV0LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV0_arg_regular :
    (barrierCase2X12XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV0LogArg).re := by
  rw [barrierCase2X12XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X12XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (284972193108636808329 / 156250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X12XV0LogArg (0) (0) (284972193108636808329 / 156250000000000000000) (16881119427 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (16881119427 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (284972193108636808329 / 156250000000000000000) (0 / 1) <
      (45668637548 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (45668637548 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X12XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (284972193108636808329 / 156250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (45668637548 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV1LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X12XV1_arg_eq :
    barrierCase2X12XV1LogArg = barrierComplex (44393358281 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV1LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV1_arg_regular :
    (barrierCase2X12XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV1LogArg).re := by
  rw [barrierCase2X12XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X12XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (1970770259465231274961 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X12XV1LogArg (1) (0) (1970770259465231274961 / 1953125000000000000000) (44393358281 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (44393358281 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (1970770259465231274961 / 1953125000000000000000) (0 / 1) <
      (15628471767 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (15628471767 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X12XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (1970770259465231274961 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (15628471767 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV2LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X12XV2_arg_eq :
    barrierCase2X12XV2LogArg = barrierComplex (76807686303 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV2LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV2_arg_regular :
    (barrierCase2X12XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV2LogArg).re := by
  rw [barrierCase2X12XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X12XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-2) (0) (5899420675220053807809 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X12XV2LogArg (-2) (0) (5899420675220053807809 / 3906250000000000000000) (76807686303 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (76807686303 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-2) (0) (5899420675220053807809 / 3906250000000000000000) (0 / 1) <
      (-12396317856 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-12396317856 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X12XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-2) (0) (5899420675220053807809 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-12396317856 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV3LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X12XV3_arg_eq :
    barrierCase2X12XV3LogArg = barrierComplex (116758730887 / 200000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV3LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV3_arg_regular :
    (barrierCase2X12XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV3LogArg).re := by
  rw [barrierCase2X12XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X12XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (13632601238342887806769 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X12XV3LogArg (-2) (0) (13632601238342887806769 / 10000000000000000000000) (116758730887 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (116758730887 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (13632601238342887806769 / 10000000000000000000000) (0 / 1) <
      (26547815511 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (26547815511 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X12XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (13632601238342887806769 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (26547815511 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV4LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X12XV4_arg_eq :
    barrierCase2X12XV4LogArg = barrierComplex (711122310479 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV4LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV4_arg_regular :
    (barrierCase2X12XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV4LogArg).re := by
  rw [barrierCase2X12XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X12XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (505694940460991273209441 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X12XV4LogArg (-2) (0) (505694940460991273209441 / 390625000000000000000000) (711122310479 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (711122310479 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (505694940460991273209441 / 390625000000000000000000) (0 / 1) <
      (-65532724513 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-65532724513 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X12XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (505694940460991273209441 / 390625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-65532724513 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV5LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X12XV5_arg_eq :
    barrierCase2X12XV5LogArg = barrierComplex (1 / 1) (-170863657653 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV5LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV5_arg_regular :
    (barrierCase2X12XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV5LogArg).re := by
  rw [barrierCase2X12XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X12XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (279194389506561585468409 / 250000000000000000000000) (-170863657653 / 500000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X12XV5LogArg (0) (0) (279194389506561585468409 / 250000000000000000000000) (1 / 1) (-170863657653 / 500000000000)
  have hratio : ((-170863657653 / 500000000000) / (1 / 1) : ℚ) = (-170863657653 / 500000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (279194389506561585468409 / 250000000000000000000000) (-170863657653 / 500000000000) <
      (70822948989 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (70822948989 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X12XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (279194389506561585468409 / 250000000000000000000000) (-170863657653 / 500000000000) : ℚ) : ℝ) <
      (70822948989 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV7LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X12XV7_arg_eq :
    barrierCase2X12XV7LogArg = barrierComplex (1 / 1) (-39430074843 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV7LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV7_arg_regular :
    (barrierCase2X12XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV7LogArg).re := by
  rw [barrierCase2X12XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X12XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (11554730802124581474649 / 10000000000000000000000) (-39430074843 / 100000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X12XV7LogArg (0) (0) (11554730802124581474649 / 10000000000000000000000) (1 / 1) (-39430074843 / 100000000000)
  have hratio : ((-39430074843 / 100000000000) / (1 / 1) : ℚ) = (-39430074843 / 100000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (11554730802124581474649 / 10000000000000000000000) (-39430074843 / 100000000000) <
      (45369325143 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (45369325143 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X12XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (11554730802124581474649 / 10000000000000000000000) (-39430074843 / 100000000000) : ℚ) : ℝ) <
      (45369325143 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV9LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X12XV9_arg_eq :
    barrierCase2X12XV9LogArg = barrierComplex (1 / 1) (-836793810557 / 2000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV9LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV9_arg_regular :
    (barrierCase2X12XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV9LogArg).re := by
  rw [barrierCase2X12XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X12XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4700223881386504404650249 / 4000000000000000000000000) (-836793810557 / 2000000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X12XV9LogArg (0) (0) (4700223881386504404650249 / 4000000000000000000000000) (1 / 1) (-836793810557 / 2000000000000)
  have hratio : ((-836793810557 / 2000000000000) / (1 / 1) : ℚ) = (-836793810557 / 2000000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4700223881386504404650249 / 4000000000000000000000000) (-836793810557 / 2000000000000) <
      (-26301451742 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-26301451742 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X12XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4700223881386504404650249 / 4000000000000000000000000) (-836793810557 / 2000000000000) : ℚ) : ℝ) <
      (-26301451742 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XV11LogArg : ℂ :=
  1 - ((Case2PointData.X12 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X12XV11_arg_eq :
    barrierCase2X12XV11LogArg = barrierComplex (1 / 1) (-538877689521 / 1250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XV11LogArg, Case2PointData.X12, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XV11_arg_regular :
    (barrierCase2X12XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XV11LogArg).re := by
  rw [barrierCase2X12XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X12XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1852889164263491273209441 / 1562500000000000000000000) (-538877689521 / 1250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X12XV11LogArg (0) (0) (1852889164263491273209441 / 1562500000000000000000000) (1 / 1) (-538877689521 / 1250000000000)
  have hratio : ((-538877689521 / 1250000000000) / (1 / 1) : ℚ) = (-538877689521 / 1250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1852889164263491273209441 / 1562500000000000000000000) (-538877689521 / 1250000000000) <
      (45070600722 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (45070600722 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X12XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1852889164263491273209441 / 1562500000000000000000000) (-538877689521 / 1250000000000) : ℚ) : ℝ) <
      (45070600722 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X12_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X12 : ℝ))).sum <
      (732863929702 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X12 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X12 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X12XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X12XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X12XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X12XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X12XP0_log_upper,
    barrierCase2X12XP1_log_upper,
    barrierCase2X12XP2_log_upper,
    barrierCase2X12XP4_log_upper,
    barrierCase2X12XP6_log_upper,
    barrierCase2X12XP8_log_upper]

private theorem barrierCase2X12_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X12 : ℝ))).sum <
      (279838728681 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X12 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X12 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X12XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X12XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X12XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X12XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X12XV0_log_upper,
    barrierCase2X12XV1_log_upper,
    barrierCase2X12XV2_log_upper,
    barrierCase2X12XV3_log_upper,
    barrierCase2X12XV4_log_upper,
    barrierCase2X12XV5_log_upper,
    barrierCase2X12XV7_log_upper,
    barrierCase2X12XV9_log_upper,
    barrierCase2X12XV11_log_upper]

private theorem barrierCase2X12_approx_upper :
    barrierCase2XApproxRat X12 (-2) (-1) (0) (4381119427 / 2500000000) (5618880573 / 5000000000) (119194207433636808329 / 100000000000000000000) + (732863929702 / 1000000000000) + (279838728681 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X12_lt : barrierCase2X (X12 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X12 : ℝ)| ≤ 1 := by norm_num [X12]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X12 hx
    (-2) (-1) (0) (4381119427 / 2500000000) (5618880573 / 5000000000) (119194207433636808329 / 100000000000000000000)
    X12_normalizations.1 X12_normalizations.2.1 X12_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X12 (-2) (-1) (0) (4381119427 / 2500000000) (5618880573 / 5000000000) (119194207433636808329 / 100000000000000000000) : ℚ) : ℝ) +
      (732863929702 / 1000000000000) + (279838728681 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X12_XP_tail_upper, barrierCase2X12_XV_tail_upper]

end InternalCatalan

end

end OAI
