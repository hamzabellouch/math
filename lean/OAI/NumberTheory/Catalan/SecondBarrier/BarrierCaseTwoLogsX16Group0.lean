import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X16XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X16 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X16XP0_arg_eq :
    barrierCase2X16XP0LogArg = barrierComplex (3398888103 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XP0LogArg, Case2PointData.X16, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XP0_arg_regular :
    (barrierCase2X16XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XP0LogArg).re := by
  rw [barrierCase2X16XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X16XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-6) (0) (11552440336714938609 / 9765625000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X16XP0LogArg (-6) (0) (11552440336714938609 / 9765625000000000000) (3398888103 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (3398888103 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-6) (0) (11552440336714938609 / 9765625000000000000) (0 / 1) <
      (372684073946 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (372684073946 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X16XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-6) (0) (11552440336714938609 / 9765625000000000000) (0 / 1) : ℚ) : ℝ) <
      (372684073946 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X16 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X16XP1_arg_eq :
    barrierCase2X16XP1LogArg = barrierComplex (8066778873 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XP1LogArg, Case2PointData.X16, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XP1_arg_regular :
    (barrierCase2X16XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XP1LogArg).re := by
  rw [barrierCase2X16XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X16XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-6) (0) (65072921385879150129 / 61035156250000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X16XP1LogArg (-6) (0) (65072921385879150129 / 61035156250000000000) (8066778873 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (8066778873 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-6) (0) (65072921385879150129 / 61035156250000000000) (0 / 1) <
      (87691037450 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (87691037450 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X16XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-6) (0) (65072921385879150129 / 61035156250000000000) (0 / 1) : ℚ) : ℝ) <
      (87691037450 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X16 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X16XP2_arg_eq :
    barrierCase2X16XP2LogArg = barrierComplex (51 / 100) (-16332075487 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XP2LogArg, Case2PointData.X16, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XP2_arg_regular :
    (barrierCase2X16XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XP2LogArg).re := by
  rw [barrierCase2X16XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X16XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (307377314713066287169 / 156250000000000000000) (-9957075487 / 22707075487) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X16XP2LogArg (0) (-1) (307377314713066287169 / 156250000000000000000) (22707075487 / 12500000000) (-9957075487 / 12500000000)
  have hratio : ((-9957075487 / 12500000000) / (22707075487 / 12500000000) : ℚ) = (-9957075487 / 22707075487) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (307377314713066287169 / 156250000000000000000) (-9957075487 / 22707075487) <
      (158235171644 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (158235171644 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X16XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (307377314713066287169 / 156250000000000000000) (-9957075487 / 22707075487) : ℚ) : ℝ) <
      (158235171644 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X16 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X16XP4_arg_eq :
    barrierCase2X16XP4LogArg = barrierComplex (111 / 400) (-39663611897 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XP4LogArg, Case2PointData.X16, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XP4_arg_regular :
    (barrierCase2X16XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XP4LogArg).re := by
  rw [barrierCase2X16XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X16XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (1621331014965839938609 / 1250000000000000000000) (6937500000 / 39663611897) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X16XP4LogArg (1) (-2) (1621331014965839938609 / 1250000000000000000000) (39663611897 / 12500000000) (111 / 200)
  have hratio : ((111 / 200) / (39663611897 / 12500000000) : ℚ) = (6937500000 / 39663611897) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (1621331014965839938609 / 1250000000000000000000) (6937500000 / 39663611897) <
      (-89765701410 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-89765701410 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X16XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (1621331014965839938609 / 1250000000000000000000) (6937500000 / 39663611897) : ℚ) : ℝ) <
      (-89765701410 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X16 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X16XP6_arg_eq :
    barrierCase2X16XP6LogArg = barrierComplex (-3017533743 / 312500000000) (-48372533743 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XP6LogArg, Case2PointData.X16, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XP6_arg_regular :
    (barrierCase2X16XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XP6LogArg).re := by
  rw [barrierCase2X16XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X16XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (233999307581657502594949 / 195312500000000000000000) (-3017533743 / 483725337430) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X16XP6LogArg (1) (-2) (233999307581657502594949 / 195312500000000000000000) (48372533743 / 15625000000) (-3017533743 / 156250000000)
  have hratio : ((-3017533743 / 156250000000) / (48372533743 / 15625000000) : ℚ) = (-3017533743 / 483725337430) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (233999307581657502594949 / 195312500000000000000000) (-3017533743 / 483725337430) <
      (-154896393950 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-154896393950 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X16XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (233999307581657502594949 / 195312500000000000000000) (-3017533743 / 483725337430) : ℚ) : ℝ) <
      (-154896393950 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X16XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X16 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X16XP8_arg_eq :
    barrierCase2X16XP8LogArg = barrierComplex (104307533743 / 312500000000) (-58952533743 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X16XP8LogArg, Case2PointData.X16, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X16XP8_arg_regular :
    (barrierCase2X16XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X16XP8LogArg).re := by
  rw [barrierCase2X16XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X16XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X16XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X16XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (358420185067502442594949 / 195312500000000000000000) (104307533743 / 589525337430) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X16XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X16XP8LogArg (1) (-2) (358420185067502442594949 / 195312500000000000000000) (58952533743 / 15625000000) (104307533743 / 156250000000)
  have hratio : ((104307533743 / 156250000000) / (58952533743 / 15625000000) : ℚ) = (104307533743 / 589525337430) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X16XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X16XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (358420185067502442594949 / 195312500000000000000000) (104307533743 / 589525337430) <
      (113196087874 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X16XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X16 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (113196087874 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X16XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X16XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (358420185067502442594949 / 195312500000000000000000) (104307533743 / 589525337430) : ℚ) : ℝ) <
      (113196087874 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X16XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
