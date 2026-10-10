import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX15Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X15XV0LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X15XV0_arg_eq :
    barrierCase2X15XV0LogArg = barrierComplex (10445138701 / 6250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV0LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV0_arg_regular :
    (barrierCase2X15XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV0LogArg).re := by
  rw [barrierCase2X15XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X15XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (109100922483127967401 / 78125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X15XV0LogArg (1) (0) (109100922483127967401 / 78125000000000000000) (10445138701 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (10445138701 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (109100922483127967401 / 78125000000000000000) (0 / 1) <
      (78056340024 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (78056340024 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X15XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (109100922483127967401 / 78125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (78056340024 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV1LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X15XV1_arg_eq :
    barrierCase2X15XV1LogArg = barrierComplex (28210416103 / 15625000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV1LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV1_arg_regular :
    (barrierCase2X15XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV1LogArg).re := by
  rw [barrierCase2X15XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X15XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (795827576704401706609 / 488281250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X15XV1LogArg (1) (0) (795827576704401706609 / 488281250000000000000) (28210416103 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (28210416103 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (795827576704401706609 / 488281250000000000000) (0 / 1) <
      (26301268451 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (26301268451 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X15XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (795827576704401706609 / 488281250000000000000) (0 / 1) : ℚ) : ℝ) <
      (26301268451 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV2LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X15XV2_arg_eq :
    barrierCase2X15XV2LogArg = barrierComplex (16353474289 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV2LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV2_arg_regular :
    (barrierCase2X15XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV2LogArg).re := by
  rw [barrierCase2X15XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X15XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-4) (0) (267436121320984055521 / 244140625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X15XV2LogArg (-4) (0) (267436121320984055521 / 244140625000000000000) (16353474289 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (16353474289 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-4) (0) (267436121320984055521 / 244140625000000000000) (0 / 1) <
      (-34126817554 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-34126817554 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X15XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-4) (0) (267436121320984055521 / 244140625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-34126817554 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV3LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X15XV3_arg_eq :
    barrierCase2X15XV3LogArg = barrierComplex (20292364681 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV3LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV3_arg_regular :
    (barrierCase2X15XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV3LogArg).re := by
  rw [barrierCase2X15XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X15XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-5) (0) (411780064346696231761 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X15XV3LogArg (-5) (0) (411780064346696231761 / 312500000000000000000) (20292364681 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (20292364681 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-5) (0) (411780064346696231761 / 312500000000000000000) (0 / 1) <
      (78671837232 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (78671837232 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X15XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-5) (0) (411780064346696231761 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (78671837232 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV4LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X15XV4_arg_eq :
    barrierCase2X15XV4LogArg = barrierComplex (108997939777 / 625000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV4LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV4_arg_regular :
    (barrierCase2X15XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV4LogArg).re := by
  rw [barrierCase2X15XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X15XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-6) (0) (11880550875630518809729 / 6103515625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X15XV4LogArg (-6) (0) (11880550875630518809729 / 6103515625000000000000) (108997939777 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (108997939777 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-6) (0) (11880550875630518809729 / 6103515625000000000000) (0 / 1) <
      (-202902127545 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-202902127545 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X15XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-6) (0) (11880550875630518809729 / 6103515625000000000000) (0 / 1) : ℚ) : ℝ) <
      (-202902127545 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV5LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X15XV5_arg_eq :
    barrierCase2X15XV5LogArg = barrierComplex (1 / 1) (-163610409339 / 250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV5LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV5_arg_regular :
    (barrierCase2X15XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV5LogArg).re := by
  rw [barrierCase2X15XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X15XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (89268366044075138416921 / 62500000000000000000000) (86389590661 / 413610409339) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X15XV5LogArg (0) (-1) (89268366044075138416921 / 62500000000000000000000) (413610409339 / 250000000000) (86389590661 / 250000000000)
  have hratio : ((86389590661 / 250000000000) / (413610409339 / 250000000000) : ℚ) = (86389590661 / 413610409339) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (89268366044075138416921 / 62500000000000000000000) (86389590661 / 413610409339) <
      (135676407036 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (135676407036 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X15XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (89268366044075138416921 / 62500000000000000000000) (86389590661 / 413610409339) : ℚ) : ℝ) <
      (135676407036 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV7LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X15XV7_arg_eq :
    barrierCase2X15XV7LogArg = barrierComplex (1 / 1) (-37756248309 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV7LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV7_arg_regular :
    (barrierCase2X15XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV7LogArg).re := by
  rw [barrierCase2X15XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X15XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (3925534286370865359481 / 2500000000000000000000) (12243751691 / 87756248309) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X15XV7LogArg (0) (-1) (3925534286370865359481 / 2500000000000000000000) (87756248309 / 50000000000) (12243751691 / 50000000000)
  have hratio : ((12243751691 / 50000000000) / (87756248309 / 50000000000) : ℚ) = (12243751691 / 87756248309) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (3925534286370865359481 / 2500000000000000000000) (12243751691 / 87756248309) <
      (62272800308 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (62272800308 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X15XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (3925534286370865359481 / 2500000000000000000000) (12243751691 / 87756248309) : ℚ) : ℝ) <
      (62272800308 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV9LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X15XV9_arg_eq :
    barrierCase2X15XV9LogArg = barrierComplex (1 / 1) (-801271491891 / 1000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV9LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV9_arg_regular :
    (barrierCase2X15XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV9LogArg).re := by
  rw [barrierCase2X15XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X15XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (1642036003717228878755881 / 1000000000000000000000000) (198728508109 / 1801271491891) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X15XV9LogArg (0) (-1) (1642036003717228878755881 / 1000000000000000000000000) (1801271491891 / 1000000000000) (198728508109 / 1000000000000)
  have hratio : ((198728508109 / 1000000000000) / (1801271491891 / 1000000000000) : ℚ) = (198728508109 / 1801271491891) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (1642036003717228878755881 / 1000000000000000000000000) (198728508109 / 1801271491891) <
      (-48533513456 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-48533513456 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X15XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (1642036003717228878755881 / 1000000000000000000000000) (198728508109 / 1801271491891) : ℚ) : ℝ) <
      (-48533513456 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X15XV11LogArg : ℂ :=
  1 - ((Case2PointData.X15 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X15XV11_arg_eq :
    barrierCase2X15XV11LogArg = barrierComplex (1 / 1) (-516002060223 / 625000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X15XV11LogArg, Case2PointData.X15, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X15XV11_arg_regular :
    (barrierCase2X15XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X15XV11LogArg).re := by
  rw [barrierCase2X15XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X15XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X15XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X15XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (656883126154380518809729 / 390625000000000000000000) (108997939777 / 1141002060223) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X15XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X15XV11LogArg (0) (-1) (656883126154380518809729 / 390625000000000000000000) (1141002060223 / 625000000000) (108997939777 / 625000000000)
  have hratio : ((108997939777 / 625000000000) / (1141002060223 / 625000000000) : ℚ) = (108997939777 / 1141002060223) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X15XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X15XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (656883126154380518809729 / 390625000000000000000000) (108997939777 / 1141002060223) <
      (77607467334 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X15XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (77607467334 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X15XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X15XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (656883126154380518809729 / 390625000000000000000000) (108997939777 / 1141002060223) : ℚ) : ℝ) <
      (77607467334 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X15_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X15 : ℝ))).sum <
      (445438127211 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X15 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X15 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X15XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X15XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X15XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X15XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X15XP0_log_upper,
    barrierCase2X15XP1_log_upper,
    barrierCase2X15XP2_log_upper,
    barrierCase2X15XP4_log_upper,
    barrierCase2X15XP6_log_upper,
    barrierCase2X15XP8_log_upper]

private theorem barrierCase2X15_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X15 : ℝ))).sum <
      (400046823052 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X15 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X15 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X15XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X15XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X15XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X15XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X15XV0_log_upper,
    barrierCase2X15XV1_log_upper,
    barrierCase2X15XV2_log_upper,
    barrierCase2X15XV3_log_upper,
    barrierCase2X15XV4_log_upper,
    barrierCase2X15XV5_log_upper,
    barrierCase2X15XV7_log_upper,
    barrierCase2X15XV9_log_upper,
    barrierCase2X15XV11_log_upper]

private theorem barrierCase2X15_approx_upper :
    barrierCase2XApproxRat X15 (-1) (-3) (0) (4195138701 / 2500000000) (804861299 / 625000000) (42599188720627967401 / 25000000000000000000) + (445438127211 / 1000000000000) + (400046823052 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X15_lt : barrierCase2X (X15 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X15 : ℝ)| ≤ 1 := by norm_num [X15]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X15 hx
    (-1) (-3) (0) (4195138701 / 2500000000) (804861299 / 625000000) (42599188720627967401 / 25000000000000000000)
    X15_normalizations.1 X15_normalizations.2.1 X15_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X15 (-1) (-3) (0) (4195138701 / 2500000000) (804861299 / 625000000) (42599188720627967401 / 25000000000000000000) : ℚ) : ℝ) +
      (445438127211 / 1000000000000) + (400046823052 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X15_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X15_XP_tail_upper, barrierCase2X15_XV_tail_upper]

end InternalCatalan

end

end OAI
