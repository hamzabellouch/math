import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X14XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X14 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X14XP2_arg_eq :
    barrierCase2X14XP2LogArg = barrierComplex (51 / 100) (-50883214851 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XP2LogArg, Case2PointData.X14, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XP2_arg_regular :
    (barrierCase2X14XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XP2LogArg).re := by
  rw [barrierCase2X14XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X14XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (3239351553573026952201 / 2500000000000000000000) (-8461071617 / 25461071617) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X14XP2LogArg (0) (-1) (3239351553573026952201 / 2500000000000000000000) (76383214851 / 50000000000) (-25383214851 / 50000000000)
  have hratio : ((-25383214851 / 50000000000) / (76383214851 / 50000000000) : ℚ) = (-8461071617 / 25461071617) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (3239351553573026952201 / 2500000000000000000000) (-8461071617 / 25461071617) <
      (267114214784 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (267114214784 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X14XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (3239351553573026952201 / 2500000000000000000000) (-8461071617 / 25461071617) : ℚ) : ℝ) <
      (267114214784 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X14 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X14XP4_arg_eq :
    barrierCase2X14XP4LogArg = barrierComplex (111 / 400) (-123573521781 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XP4LogArg, Case2PointData.X14, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XP4_arg_regular :
    (barrierCase2X14XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XP4LogArg).re := by
  rw [barrierCase2X14XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X14XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (16040477785359281411961 / 10000000000000000000000) (250000000 / 1113274971) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X14XP4LogArg (0) (-2) (16040477785359281411961 / 10000000000000000000000) (123573521781 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (123573521781 / 50000000000) : ℚ) = (250000000 / 1113274971) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (16040477785359281411961 / 10000000000000000000000) (250000000 / 1113274971) <
      (-83939557685 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-83939557685 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X14XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (16040477785359281411961 / 10000000000000000000000) (250000000 / 1113274971) : ℚ) : ℝ) <
      (-83939557685 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X14 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X14XP6_arg_eq :
    barrierCase2X14XP6LogArg = barrierComplex (35392294061 / 1250000000000) (-146027705939 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XP6LogArg, Case2PointData.X14, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XP6_arg_regular :
    (barrierCase2X14XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XP6LogArg).re := by
  rw [barrierCase2X14XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X14XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (2133661704659605883043821 / 1562500000000000000000000) (35392294061 / 1460277059390) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X14XP6LogArg (0) (-2) (2133661704659605883043821 / 1562500000000000000000000) (146027705939 / 62500000000) (35392294061 / 625000000000)
  have hratio : ((35392294061 / 625000000000) / (146027705939 / 62500000000) : ℚ) = (35392294061 / 1460277059390) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (2133661704659605883043821 / 1562500000000000000000000) (35392294061 / 1460277059390) <
      (-143106100436 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-143106100436 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X14XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (-2) (2133661704659605883043821 / 1562500000000000000000000) (35392294061 / 1460277059390) : ℚ) : ℝ) <
      (-143106100436 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X14 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X14XP8_arg_eq :
    barrierCase2X14XP8LogArg = barrierComplex (369767705939 / 1250000000000) (-188347705939 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XP8LogArg, Case2PointData.X14, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XP8_arg_regular :
    (barrierCase2X14XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XP8LogArg).re := by
  rw [barrierCase2X14XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X14XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (3684213989603792363043821 / 3125000000000000000000000) (369767705939 / 1883477059390) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X14XP8LogArg (1) (-2) (3684213989603792363043821 / 3125000000000000000000000) (188347705939 / 62500000000) (369767705939 / 625000000000)
  have hratio : ((369767705939 / 625000000000) / (188347705939 / 62500000000) : ℚ) = (369767705939 / 1883477059390) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (3684213989603792363043821 / 3125000000000000000000000) (369767705939 / 1883477059390) <
      (116151232235 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (116151232235 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X14XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (3684213989603792363043821 / 3125000000000000000000000) (369767705939 / 1883477059390) : ℚ) : ℝ) <
      (116151232235 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XP8_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV5LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 5 (0, 0)).1

private theorem barrierCase2X14XV5_arg_eq :
    barrierCase2X14XV5LogArg = barrierComplex (1 / 1) (-283492197027 / 500000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV5LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV5_arg_regular :
    (barrierCase2X14XV5LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV5LogArg).re := by
  rw [barrierCase2X14XV5_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV5_weight_eq :
    (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV5_error :
    |((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X14XV5LogArg).re -
      ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (330367825775195387638729 / 250000000000000000000000) (216507802973 / 783492197027) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV5_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X14XV5LogArg (0) (-1) (330367825775195387638729 / 250000000000000000000000) (783492197027 / 500000000000) (216507802973 / 500000000000)
  have hratio : ((216507802973 / 500000000000) / (783492197027 / 500000000000) : ℚ) = (216507802973 / 783492197027) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV5_approx_upper :
    barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (330367825775195387638729 / 250000000000000000000000) (216507802973 / 783492197027) <
      (118136892273 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV5_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 5 (0, 0)) <
      (118136892273 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X14XV5LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV5_error).2
  have ha : ((barrierWeightedComplexLogRat (13619357 / 100000000) (600749 / 3125000) (0) (-1) (330367825775195387638729 / 250000000000000000000000) (216507802973 / 783492197027) : ℚ) : ℝ) <
      (118136892273 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV5_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV7LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 7 (0, 0)).1

private theorem barrierCase2X14XV7_arg_eq :
    barrierCase2X14XV7LogArg = barrierComplex (1 / 1) (-65421276237 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV7LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV7_arg_regular :
    (barrierCase2X14XV7LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV7LogArg).re := by
  rw [barrierCase2X14XV7_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV7_weight_eq :
    (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV7_error :
    |((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X14XV7LogArg).re -
      ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (14279943384477860880169 / 10000000000000000000000) (34578723763 / 165421276237) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV7_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X14XV7LogArg (0) (-1) (14279943384477860880169 / 10000000000000000000000) (165421276237 / 100000000000) (34578723763 / 100000000000)
  have hratio : ((34578723763 / 100000000000) / (165421276237 / 100000000000) : ℚ) = (34578723763 / 165421276237) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV7_approx_upper :
    barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (14279943384477860880169 / 10000000000000000000000) (34578723763 / 165421276237) <
      (59531713827 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV7_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 7 (0, 0)) <
      (59531713827 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X14XV7LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV7_error).2
  have ha : ((barrierWeightedComplexLogRat (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (14279943384477860880169 / 10000000000000000000000) (34578723763 / 165421276237) : ℚ) : ℝ) <
      (59531713827 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV7_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
