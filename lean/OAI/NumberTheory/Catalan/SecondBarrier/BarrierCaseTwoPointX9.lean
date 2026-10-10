import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX9Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X9XV0LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X9XV0_arg_eq :
    barrierCase2X9XV0LogArg = barrierComplex (7015974031 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV0LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV0_arg_regular :
    (barrierCase2X9XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV0LogArg).re := by
  rw [barrierCase2X9XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X9XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (49223891603666388961 / 39062500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X9XV0LogArg (0) (0) (49223891603666388961 / 39062500000000000000) (7015974031 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (7015974031 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (49223891603666388961 / 39062500000000000000) (0 / 1) <
      (17571517521 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (17571517521 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X9XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (49223891603666388961 / 39062500000000000000) (0 / 1) : ℚ) : ℝ) <
      (17571517521 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV1LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X9XV1_arg_eq :
    barrierCase2X9XV1LogArg = barrierComplex (17922922093 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV1LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV1_arg_regular :
    (barrierCase2X9XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV1LogArg).re := by
  rw [barrierCase2X9XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X9XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (321231136351747500649 / 244140625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X9XV1LogArg (0) (0) (321231136351747500649 / 244140625000000000000) (17922922093 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (17922922093 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (321231136351747500649 / 244140625000000000000) (0 / 1) <
      (6108048055 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (6108048055 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X9XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (321231136351747500649 / 244140625000000000000) (0 / 1) : ℚ) : ℝ) <
      (6108048055 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV2LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X9XV2_arg_eq :
    barrierCase2X9XV2LogArg = barrierComplex (54074285659 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV2LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV2_arg_regular :
    (barrierCase2X9XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV2LogArg).re := by
  rw [barrierCase2X9XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X9XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (2924028369531133064281 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X9XV2LogArg (-1) (0) (2924028369531133064281 / 1953125000000000000000) (54074285659 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (54074285659 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (2924028369531133064281 / 1953125000000000000000) (0 / 1) <
      (-3685934721 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-3685934721 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X9XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (2924028369531133064281 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-3685934721 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV3LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X9XV3_arg_eq :
    barrierCase2X9XV3LogArg = barrierComplex (85446493411 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV3LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV3_arg_regular :
    (barrierCase2X9XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV3LogArg).re := by
  rw [barrierCase2X9XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X9XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-1) (0) (7301103236236066414921 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X9XV3LogArg (-1) (0) (7301103236236066414921 / 5000000000000000000000) (85446493411 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (85446493411 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-1) (0) (7301103236236066414921 / 5000000000000000000000) (0 / 1) <
      (7758037582 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (7758037582 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X9XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-1) (0) (7301103236236066414921 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (7758037582 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV4LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X9XV4_arg_eq :
    barrierCase2X9XV4LogArg = barrierComplex (530785194187 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV4LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV4_arg_regular :
    (barrierCase2X9XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV4LogArg).re := by
  rw [barrierCase2X9XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X9XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-1) (0) (281732922368131298590969 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X9XV4LogArg (-1) (0) (281732922368131298590969 / 195312500000000000000000) (530785194187 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (530785194187 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-1) (0) (281732922368131298590969 / 195312500000000000000000) (0 / 1) <
      (-18983399454 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-18983399454 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X9XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-1) (0) (281732922368131298590969 / 195312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-18983399454 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV5LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X9XV5_arg_eq :
    barrierCase2X9XV5LogArg = barrierComplex (1 / 1) (-29872987209 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV5LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV5_arg_regular :
    (barrierCase2X9XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV5LogArg).re := by
  rw [barrierCase2X9XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X9XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (63392395364789077609681 / 62500000000000000000000) (-29872987209 / 250000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X9XV5LogArg (0) (0) (63392395364789077609681 / 62500000000000000000000) (1 / 1) (-29872987209 / 250000000000)
  have hratio : ((-29872987209 / 250000000000) / (1 / 1) : ℚ) = (-29872987209 / 250000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (63392395364789077609681 / 62500000000000000000000) (-29872987209 / 250000000000) <
      (23828123593 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (23828123593 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X9XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (63392395364789077609681 / 62500000000000000000000) (-29872987209 / 250000000000) : ℚ) : ℝ) <
      (23828123593 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV5_approx_upper using 1
    norm_num
  linarith






def barrierCase2X9XV7LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X9XV7_arg_eq :
    barrierCase2X9XV7LogArg = barrierComplex (1 / 1) (-6893766279 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV7LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV7_arg_regular :
    (barrierCase2X9XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV7LogArg).re := by
  rw [barrierCase2X9XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X9XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2547524013509477505841 / 2500000000000000000000) (-6893766279 / 50000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X9XV7LogArg (0) (0) (2547524013509477505841 / 2500000000000000000000) (1 / 1) (-6893766279 / 50000000000)
  have hratio : ((-6893766279 / 50000000000) / (1 / 1) : ℚ) = (-6893766279 / 50000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2547524013509477505841 / 2500000000000000000000) (-6893766279 / 50000000000) <
      (19205581007 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (19205581007 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X9XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2547524013509477505841 / 2500000000000000000000) (-6893766279 / 50000000000) : ℚ) : ℝ) <
      (19205581007 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV9LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X9XV9_arg_eq :
    barrierCase2X9XV9LogArg = barrierComplex (1 / 1) (-146301039921 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV9LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV9_arg_regular :
    (barrierCase2X9XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV9LogArg).re := by
  rw [barrierCase2X9XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X9XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1021403994281966035686241 / 1000000000000000000000000) (-146301039921 / 1000000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X9XV9LogArg (0) (0) (1021403994281966035686241 / 1000000000000000000000000) (1 / 1) (-146301039921 / 1000000000000)
  have hratio : ((-146301039921 / 1000000000000) / (1 / 1) : ℚ) = (-146301039921 / 1000000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1021403994281966035686241 / 1000000000000000000000000) (-146301039921 / 1000000000000) <
      (-9006883590 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-9006883590 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X9XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1021403994281966035686241 / 1000000000000000000000000) (-146301039921 / 1000000000000) : ℚ) : ℝ) <
      (-9006883590 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XV11LogArg : ℂ :=
  1 - ((Case2PointData.X9 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X9XV11_arg_eq :
    barrierCase2X9XV11LogArg = barrierComplex (1 / 1) (-94214805813 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XV11LogArg, Case2PointData.X9, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XV11_arg_regular :
    (barrierCase2X9XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XV11LogArg).re := by
  rw [barrierCase2X9XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X9XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (399501429634381298590969 / 390625000000000000000000) (-94214805813 / 625000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X9XV11LogArg (0) (0) (399501429634381298590969 / 390625000000000000000000) (1 / 1) (-94214805813 / 625000000000)
  have hratio : ((-94214805813 / 625000000000) / (1 / 1) : ℚ) = (-94214805813 / 625000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (399501429634381298590969 / 390625000000000000000000) (-94214805813 / 625000000000) <
      (16360769931 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (16360769931 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X9XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (399501429634381298590969 / 390625000000000000000000) (-94214805813 / 625000000000) : ℚ) : ℝ) <
      (16360769931 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XV11_approx_upper using 1
    norm_num
  linarith





open Case2PointData

private theorem barrierCase2X9_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X9 : ℝ))).sum <
      (1111759233350 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X9 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X9 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X9XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X9XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X9XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X9XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X9XP0_log_upper,
    barrierCase2X9XP1_log_upper,
    barrierCase2X9XP2_log_upper,
    barrierCase2X9XP4_log_upper,
    barrierCase2X9XP6_log_upper,
    barrierCase2X9XP8_log_upper]

private theorem barrierCase2X9_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X9 : ℝ))).sum <
      (109543450865 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X9 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X9 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X9XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X9XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X9XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X9XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X9XV0_log_upper,
    barrierCase2X9XV1_log_upper,
    barrierCase2X9XV2_log_upper,
    barrierCase2X9XV3_log_upper,
    barrierCase2X9XV4_log_upper,
    barrierCase2X9XV5_log_upper,
    barrierCase2X9XV7_log_upper,
    barrierCase2X9XV9_log_upper,
    barrierCase2X9XV11_log_upper]

private theorem barrierCase2X9_approx_upper :
    barrierCase2XApproxRat X9 (-3) (-1) (0) (765974031 / 625000000) (4234025969 / 2500000000) (25586716216166388961 / 25000000000000000000) + (1111759233350 / 1000000000000) + (109543450865 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X9_lt : barrierCase2X (X9 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X9 : ℝ)| ≤ 1 := by norm_num [X9]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X9 hx
    (-3) (-1) (0) (765974031 / 625000000) (4234025969 / 2500000000) (25586716216166388961 / 25000000000000000000)
    X9_normalizations.1 X9_normalizations.2.1 X9_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X9 (-3) (-1) (0) (765974031 / 625000000) (4234025969 / 2500000000) (25586716216166388961 / 25000000000000000000) : ℚ) : ℝ) +
      (1111759233350 / 1000000000000) + (109543450865 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X9_XP_tail_upper, barrierCase2X9_XV_tail_upper]

end InternalCatalan

end

end OAI
