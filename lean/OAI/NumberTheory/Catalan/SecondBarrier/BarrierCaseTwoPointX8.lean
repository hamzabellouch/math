import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX8Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X8XV0LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X8XV0_arg_eq :
    barrierCase2X8XV0LogArg = barrierComplex (1363768813 / 1562500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV0LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV0_arg_regular :
    (barrierCase2X8XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV0LogArg).re := by
  rw [barrierCase2X8XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X8XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-1) (0) (1859865375311428969 / 1220703125000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X8XV0LogArg (-1) (0) (1859865375311428969 / 1220703125000000000) (1363768813 / 1562500000) (0 / 1)
  have hratio : ((0 / 1) / (1363768813 / 1562500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-1) (0) (1859865375311428969 / 1220703125000000000) (0 / 1) <
      (-20676254207 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (-20676254207 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X8XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (-1) (0) (1859865375311428969 / 1220703125000000000) (0 / 1) : ℚ) : ℝ) <
      (-20676254207 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV1LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X8XV1_arg_eq :
    barrierCase2X8XV1LogArg = barrierComplex (3310056439 / 3906250000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV1LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV1_arg_regular :
    (barrierCase2X8XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV1LogArg).re := by
  rw [barrierCase2X8XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X8XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-1) (0) (10956473629365360721 / 7629394531250000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X8XV1LogArg (-1) (0) (10956473629365360721 / 7629394531250000000) (3310056439 / 3906250000) (0 / 1)
  have hratio : ((0 / 1) / (3310056439 / 3906250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-1) (0) (10956473629365360721 / 7629394531250000000) (0 / 1) <
      (-7372512922 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (-7372512922 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X8XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (-1) (0) (10956473629365360721 / 7629394531250000000) (0 / 1) : ℚ) : ℝ) <
      (-7372512922 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV2LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X8XV2_arg_eq :
    barrierCase2X8XV2LogArg = barrierComplex (17811043057 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV2LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV2_arg_regular :
    (barrierCase2X8XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV2LogArg).re := by
  rw [barrierCase2X8XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X8XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (317233254778307905249 / 244140625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X8XV2LogArg (0) (0) (317233254778307905249 / 244140625000000000000) (17811043057 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (17811043057 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (317233254778307905249 / 244140625000000000000) (0 / 1) <
      (3333108722 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (3333108722 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X8XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (0) (0) (317233254778307905249 / 244140625000000000000) (0 / 1) : ℚ) : ℝ) <
      (3333108722 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV3LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X8XV3_arg_eq :
    barrierCase2X8XV3LogArg = barrierComplex (28775892553 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV3LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV3_arg_regular :
    (barrierCase2X8XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV3LogArg).re := by
  rw [barrierCase2X8XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X8XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (828051992221800857809 / 625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X8XV3LogArg (0) (0) (828051992221800857809 / 625000000000000000000) (28775892553 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (28775892553 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (828051992221800857809 / 625000000000000000000) (0 / 1) <
      (-6938348917 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (-6938348917 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X8XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (0) (0) (828051992221800857809 / 625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-6938348917 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV4LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X8XV4_arg_eq :
    barrierCase2X8XV4LogArg = barrierComplex (180693936001 / 156250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV4LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV4_arg_regular :
    (barrierCase2X8XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV4LogArg).re := by
  rw [barrierCase2X8XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X8XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (32650298507533483872001 / 24414062500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X8XV4LogArg (0) (0) (32650298507533483872001 / 24414062500000000000000) (180693936001 / 156250000000) (0 / 1)
  have hratio : ((0 / 1) / (180693936001 / 156250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (32650298507533483872001 / 24414062500000000000000) (0 / 1) <
      (16886683324 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (16886683324 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X8XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (0) (0) (32650298507533483872001 / 24414062500000000000000) (0 / 1) : ℚ) : ℝ) <
      (16886683324 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV5LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X8XV5_arg_eq :
    barrierCase2X8XV5LogArg = barrierComplex (1 / 1) (7750516293 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV5LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV5_arg_regular :
    (barrierCase2X8XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV5LogArg).re := by
  rw [barrierCase2X8XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X8XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (3966320502808058461849 / 3906250000000000000000) (7750516293 / 62500000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X8XV5LogArg (0) (0) (3966320502808058461849 / 3906250000000000000000) (1 / 1) (7750516293 / 62500000000)
  have hratio : ((7750516293 / 62500000000) / (1 / 1) : ℚ) = (7750516293 / 62500000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (3966320502808058461849 / 3906250000000000000000) (7750516293 / 62500000000) <
      (-22678997583 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (-22678997583 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X8XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (3966320502808058461849 / 3906250000000000000000) (7750516293 / 62500000000) : ℚ) : ℝ) <
      (-22678997583 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2X8XV7LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X8XV7_arg_eq :
    barrierCase2X8XV7LogArg = barrierComplex (1 / 1) (1788580683 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV7LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV7_arg_regular :
    (barrierCase2X8XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV7LogArg).re := by
  rw [barrierCase2X8XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X8XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (159449020859600746489 / 156250000000000000000) (1788580683 / 12500000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X8XV7LogArg (0) (0) (159449020859600746489 / 156250000000000000000) (1 / 1) (1788580683 / 12500000000)
  have hratio : ((1788580683 / 12500000000) / (1 / 1) : ℚ) = (1788580683 / 12500000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (159449020859600746489 / 156250000000000000000) (1788580683 / 12500000000) <
      (-23040390503 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (-23040390503 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X8XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (159449020859600746489 / 156250000000000000000) (1788580683 / 12500000000) : ℚ) : ℝ) <
      (-23040390503 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV9LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X8XV9_arg_eq :
    barrierCase2X8XV9LogArg = barrierComplex (1 / 1) (37957656717 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV9LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV9_arg_regular :
    (barrierCase2X8XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV9LogArg).re := by
  rw [barrierCase2X8XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X8XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (63940783703445615218089 / 62500000000000000000000) (37957656717 / 250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X8XV9LogArg (0) (0) (63940783703445615218089 / 62500000000000000000000) (1 / 1) (37957656717 / 250000000000)
  have hratio : ((37957656717 / 250000000000) / (1 / 1) : ℚ) = (37957656717 / 250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (63940783703445615218089 / 62500000000000000000000) (37957656717 / 250000000000) <
      (8593302125 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (8593302125 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X8XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (63940783703445615218089 / 62500000000000000000000) (37957656717 / 250000000000) : ℚ) : ℝ) <
      (8593302125 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XV11LogArg : ℂ :=
  1 - ((Case2PointData.X8 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X8XV11_arg_eq :
    barrierCase2X8XV11LogArg = barrierComplex (1 / 1) (24443936001 / 156250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XV11LogArg, Case2PointData.X8, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XV11_arg_regular :
    (barrierCase2X8XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XV11LogArg).re := by
  rw [barrierCase2X8XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X8XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (25011568507220983872001 / 24414062500000000000000) (24443936001 / 156250000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X8XV11LogArg (0) (0) (25011568507220983872001 / 24414062500000000000000) (1 / 1) (24443936001 / 156250000000)
  have hratio : ((24443936001 / 156250000000) / (1 / 1) : ℚ) = (24443936001 / 156250000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (25011568507220983872001 / 24414062500000000000000) (24443936001 / 156250000000) <
      (-16725459883 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (-16725459883 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X8XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (25011568507220983872001 / 24414062500000000000000) (24443936001 / 156250000000) : ℚ) : ℝ) <
      (-16725459883 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2X8_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X8 : ℝ))).sum <
      (659260384890 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X8 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X8 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X8XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X8XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X8XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X8XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X8XP0_log_upper,
    barrierCase2X8XP1_log_upper,
    barrierCase2X8XP2_log_upper,
    barrierCase2X8XP4_log_upper,
    barrierCase2X8XP6_log_upper,
    barrierCase2X8XP8_log_upper]

private theorem barrierCase2X8_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X8 : ℝ))).sum <
      (-122470415688 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X8 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X8 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X8XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X8XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X8XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X8XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X8XV0_log_upper,
    barrierCase2X8XV1_log_upper,
    barrierCase2X8XV2_log_upper,
    barrierCase2X8XV3_log_upper,
    barrierCase2X8XV4_log_upper,
    barrierCase2X8XV5_log_upper,
    barrierCase2X8XV7_log_upper,
    barrierCase2X8XV9_log_upper,
    barrierCase2X8XV11_log_upper]

private theorem barrierCase2X8_approx_upper :
    barrierCase2XApproxRat X8 (-3) (0) (0) (198731187 / 156250000) (1448731187 / 1250000000) (1601994084686428969 / 1562500000000000000) + (659260384890 / 1000000000000) + (-122470415688 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X8_lt : barrierCase2X (X8 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X8 : ℝ)| ≤ 1 := by norm_num [X8]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X8 hx
    (-3) (0) (0) (198731187 / 156250000) (1448731187 / 1250000000) (1601994084686428969 / 1562500000000000000)
    X8_normalizations.1 X8_normalizations.2.1 X8_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X8 (-3) (0) (0) (198731187 / 156250000) (1448731187 / 1250000000) (1601994084686428969 / 1562500000000000000) : ℚ) : ℝ) +
      (659260384890 / 1000000000000) + (-122470415688 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X8_XP_tail_upper, barrierCase2X8_XV_tail_upper]

end InternalCatalan

end

end OAI
