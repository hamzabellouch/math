import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X18XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X18 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X18XP0_arg_eq :
    barrierCase2X18XP0LogArg = barrierComplex (1369 / 400) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X18XP0LogArg, Case2PointData.X18, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X18XP0_arg_regular :
    (barrierCase2X18XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X18XP0LogArg).re := by
  rw [barrierCase2X18XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X18XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X18XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X18XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (1874161 / 1280000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X18XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X18XP0LogArg (3) (0) (1874161 / 1280000) (1369 / 400) (0 / 1)
  have hratio : ((0 / 1) / (1369 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X18XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X18XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (1874161 / 1280000) (0 / 1) <
      (-229795262468 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X18XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-229795262468 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X18XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X18XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (1874161 / 1280000) (0 / 1) : ℚ) : ℝ) <
      (-229795262468 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X18XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X18XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X18 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X18XP1_arg_eq :
    barrierCase2X18XP1LogArg = barrierComplex (9409 / 2500) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X18XP1LogArg, Case2PointData.X18, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X18XP1_arg_regular :
    (barrierCase2X18XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X18XP1LogArg).re := by
  rw [barrierCase2X18XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X18XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X18XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X18XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (88529281 / 50000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X18XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X18XP1LogArg (3) (0) (88529281 / 50000000) (9409 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (9409 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X18XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X18XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (88529281 / 50000000) (0 / 1) <
      (-56766090340 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X18XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-56766090340 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X18XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X18XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (88529281 / 50000000) (0 / 1) : ℚ) : ℝ) <
      (-56766090340 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X18XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X18XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X18 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X18XP2_arg_eq :
    barrierCase2X18XP2LogArg = barrierComplex (51 / 100) (7 / 5) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X18XP2LogArg, Case2PointData.X18, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X18XP2_arg_regular :
    (barrierCase2X18XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X18XP2LogArg).re := by
  rw [barrierCase2X18XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X18XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X18XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X18XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (22201 / 20000) (89 / 191) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X18XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X18XP2LogArg (1) (1) (22201 / 20000) (191 / 100) (89 / 100)
  have hratio : ((89 / 100) / (191 / 100) : ℚ) = (89 / 191) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X18XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X18XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (22201 / 20000) (89 / 191) <
      (-654036142715 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X18XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-654036142715 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X18XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X18XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (22201 / 20000) (89 / 191) : ℚ) : ℝ) <
      (-654036142715 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X18XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X18XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X18 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X18XP4_arg_eq :
    barrierCase2X18XP4LogArg = barrierComplex (111 / 400) (17 / 10) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X18XP4LogArg, Case2PointData.X18, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X18XP4_arg_regular :
    (barrierCase2X18XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X18XP4LogArg).re := by
  rw [barrierCase2X18XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X18XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X18XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X18XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (474721 / 320000) (-111 / 680) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X18XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X18XP4LogArg (1) (2) (474721 / 320000) (17 / 5) (-111 / 200)
  have hratio : ((-111 / 200) / (17 / 5) : ℚ) = (-111 / 680) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X18XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X18XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (474721 / 320000) (-111 / 680) <
      (77879123989 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X18XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (77879123989 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X18XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X18XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (474721 / 320000) (-111 / 680) : ℚ) : ℝ) <
      (77879123989 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X18XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X18XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X18 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X18XP6_arg_eq :
    barrierCase2X18XP6LogArg = barrierComplex (21629 / 62500) (6279 / 3125) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X18XP6LogArg, Case2PointData.X18, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X18XP6_arg_regular :
    (barrierCase2X18XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X18XP6LogArg).re := by
  rw [barrierCase2X18XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X18XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X18XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X18XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (2) (2) (16238150041 / 15625000000) (-21629 / 125580) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X18XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X18XP6LogArg (2) (2) (16238150041 / 15625000000) (12558 / 3125) (-21629 / 31250)
  have hratio : ((-21629 / 31250) / (12558 / 3125) : ℚ) = (-21629 / 125580) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X18XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X18XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (2) (2) (16238150041 / 15625000000) (-21629 / 125580) <
      (102035215306 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X18XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (102035215306 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X18XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X18XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (2) (2) (16238150041 / 15625000000) (-21629 / 125580) : ℚ) : ℝ) <
      (102035215306 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X18XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X18XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X18 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X18XP8_arg_eq :
    barrierCase2X18XP8LogArg = barrierComplex (-1371 / 62500) (5221 / 3125) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X18XP8LogArg, Case2PointData.X18, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X18XP8_arg_regular :
    (barrierCase2X18XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X18XP8LogArg).re := by
  rw [barrierCase2X18XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X18XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X18XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X18XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (10905416041 / 7812500000) (1371 / 104420) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X18XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X18XP8LogArg (1) (2) (10905416041 / 7812500000) (10442 / 3125) (1371 / 31250)
  have hratio : ((1371 / 31250) / (10442 / 3125) : ℚ) = (1371 / 104420) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X18XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X18XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (10905416041 / 7812500000) (1371 / 104420) <
      (-154807766094 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X18XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X18 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-154807766094 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X18XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X18XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (10905416041 / 7812500000) (1371 / 104420) : ℚ) : ℝ) <
      (-154807766094 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X18XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
