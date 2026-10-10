import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX11Group0
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X11XV0LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X11XV0_arg_eq :
    barrierCase2X11XV0LogArg = barrierComplex (3927046621 / 3125000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV0LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV0_arg_regular :
    (barrierCase2X11XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV0LogArg).re := by
  rw [barrierCase2X11XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X11XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X11XV0LogArg (0) (0) (15421695163507517641 / 9765625000000000000) (3927046621 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (3927046621 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1) <
      (34723108870 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (34723108870 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X11XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (34723108870 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV1LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X11XV1_arg_eq :
    barrierCase2X11XV1LogArg = barrierComplex (10218639863 / 7812500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV1LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV1_arg_regular :
    (barrierCase2X11XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV1LogArg).re := by
  rw [barrierCase2X11XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X11XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X11XV1LogArg (0) (0) (104420600649692658769 / 61035156250000000000) (10218639863 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (10218639863 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1) <
      (11952199419 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (11952199419 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X11XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (11952199419 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV2LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X11XV2_arg_eq :
    barrierCase2X11XV2LogArg = barrierComplex (22427487169 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV2LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV2_arg_regular :
    (barrierCase2X11XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV2LogArg).re := by
  rw [barrierCase2X11XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X11XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X11XV2LogArg (-1) (0) (502992180715659634561 / 488281250000000000000) (22427487169 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (22427487169 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1) <
      (-8443901317 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-8443901317 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X11XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1) : ℚ) : ℝ) <
      (-8443901317 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV3LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X11XV3_arg_eq :
    barrierCase2X11XV3LogArg = barrierComplex (34761114201 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV3LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV3_arg_regular :
    (barrierCase2X11XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV3LogArg).re := by
  rw [barrierCase2X11XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X11XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X11XV3LogArg (-2) (0) (1208335060494963868401 / 625000000000000000000) (34761114201 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (34761114201 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1) <
      (17931291230 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (17931291230 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X11XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-2) (0) (1208335060494963868401 / 625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (17931291230 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV4LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X11XV4_arg_eq :
    barrierCase2X11XV4LogArg = barrierComplex (213848265617 / 312500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV4LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV4_arg_regular :
    (barrierCase2X11XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV4LogArg).re := by
  rw [barrierCase2X11XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X11XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X11XV4LogArg (-2) (0) (45731080707398984390689 / 24414062500000000000000) (213848265617 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (213848265617 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1) <
      (-44072054751 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-44072054751 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X11XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-2) (0) (45731080707398984390689 / 24414062500000000000000) (0 / 1) : ℚ) : ℝ) <
      (-44072054751 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV5LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X11XV5_arg_eq :
    barrierCase2X11XV5LogArg = barrierComplex (1 / 1) (-31279818219 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV5LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV5_arg_regular :
    (barrierCase2X11XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV5LogArg).re := by
  rw [barrierCase2X11XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X11XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X11XV5LogArg (0) (0) (16603427027813684331961 / 15625000000000000000000) (1 / 1) (-31279818219 / 125000000000)
  have hratio : ((-31279818219 / 125000000000) / (1 / 1) : ℚ) = (-31279818219 / 125000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000) <
      (51273767201 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (51273767201 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X11XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (0) (16603427027813684331961 / 15625000000000000000000) (-31279818219 / 125000000000) : ℚ) : ℝ) <
      (51273767201 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV7LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X11XV7_arg_eq :
    barrierCase2X11XV7LogArg = barrierComplex (1 / 1) (-7218419589 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV7LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV7_arg_regular :
    (barrierCase2X11XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV7LogArg).re := by
  rw [barrierCase2X11XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X11XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X11XV7LogArg (0) (0) (677105581362858928921 / 625000000000000000000) (1 / 1) (-7218419589 / 25000000000)
  have hratio : ((-7218419589 / 25000000000) / (1 / 1) : ℚ) = (-7218419589 / 25000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000) <
      (36154964505 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (36154964505 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X11XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000) : ℚ) : ℝ) <
      (36154964505 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV7_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV9LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X11XV9_arg_eq :
    barrierCase2X11XV9LogArg = barrierComplex (1 / 1) (-153190904611 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV9LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV9_arg_regular :
    (barrierCase2X11XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV9LogArg).re := by
  rw [barrierCase2X11XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X11XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X11XV9LogArg (0) (0) (273467453255536501061321 / 250000000000000000000000) (1 / 1) (-153190904611 / 500000000000)
  have hratio : ((-153190904611 / 500000000000) / (1 / 1) : ℚ) = (-153190904611 / 500000000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000) <
      (-19209034814 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-19209034814 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X11XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000) : ℚ) : ℝ) <
      (-19209034814 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XV11LogArg : ℂ :=
  1 - ((Case2PointData.X11 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X11XV11_arg_eq :
    barrierCase2X11XV11LogArg = barrierComplex (1 / 1) (-98651734383 / 312500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XV11LogArg, Case2PointData.X11, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XV11_arg_regular :
    (barrierCase2X11XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XV11LogArg).re := by
  rw [barrierCase2X11XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X11XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X11XV11LogArg (0) (0) (107388414696773984390689 / 97656250000000000000000) (1 / 1) (-98651734383 / 312500000000)
  have hratio : ((-98651734383 / 312500000000) / (1 / 1) : ℚ) = (-98651734383 / 312500000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000) <
      (33689942023 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (33689942023 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X11XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000) : ℚ) : ℝ) <
      (33689942023 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X11_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X11 : ℝ))).sum <
      (872063380780 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X11 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X11XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X11XP0_log_upper,
    barrierCase2X11XP1_log_upper,
    barrierCase2X11XP2_log_upper,
    barrierCase2X11XP4_log_upper,
    barrierCase2X11XP6_log_upper,
    barrierCase2X11XP8_log_upper]

private theorem barrierCase2X11_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X11 : ℝ))).sum <
      (215909921281 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X11 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X11XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X11XV0_log_upper,
    barrierCase2X11XV1_log_upper,
    barrierCase2X11XV2_log_upper,
    barrierCase2X11XV3_log_upper,
    barrierCase2X11XV4_log_upper,
    barrierCase2X11XV5_log_upper,
    barrierCase2X11XV7_log_upper,
    barrierCase2X11XV9_log_upper,
    barrierCase2X11XV11_log_upper]

private theorem barrierCase2X11_approx_upper :
    barrierCase2XApproxRat X11 (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) + (872063380780 / 1000000000000) + (215909921281 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X11_lt : barrierCase2X (X11 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X11 : ℝ)| ≤ 1 := by norm_num [X11]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X11 hx
    (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000)
    X11_normalizations.1 X11_normalizations.2.1 X11_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X11 (-2) (-1) (0) (802046621 / 625000000) (1697953379 / 1250000000) (6893278782257517641 / 6250000000000000000) : ℚ) : ℝ) +
      (872063380780 / 1000000000000) + (215909921281 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X11_XP_tail_upper, barrierCase2X11_XV_tail_upper]

end InternalCatalan

end

end OAI
