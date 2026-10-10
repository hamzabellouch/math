import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X2XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP0_arg_eq :
    barrierCase2X2XP0LogArg = barrierComplex (301591195761 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP0LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP0_arg_regular :
    (barrierCase2X2XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP0LogArg).re := by
  rw [barrierCase2X2XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X2XP0LogArg (3) (0) (90957249360549824369121 / 80000000000000000000000) (301591195761 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (301591195761 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1) <
      (-206174764969 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-206174764969 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X2XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (90957249360549824369121 / 80000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-206174764969 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP1_arg_eq :
    barrierCase2X2XP1LogArg = barrierComplex (828490364751 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP1LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP1_arg_regular :
    (barrierCase2X2XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP1LogArg).re := by
  rw [barrierCase2X2XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X2XP1LogArg (3) (0) (686396284485245023292001 / 500000000000000000000000) (828490364751 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (828490364751 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1) <
      (-51316735570 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-51316735570 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X2XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (686396284485245023292001 / 500000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-51316735570 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP2_arg_eq :
    barrierCase2X2XP2LogArg = barrierComplex (51 / 100) (53258139431 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP2LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP2_arg_regular :
    (barrierCase2X2XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP2LogArg).re := by
  rw [barrierCase2X2XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X2XP2LogArg (0) (1) (3486679415651837003761 / 2500000000000000000000) (78758139431 / 50000000000) (27758139431 / 50000000000)
  have hratio : ((27758139431 / 50000000000) / (78758139431 / 50000000000) : ℚ) = (27758139431 / 78758139431) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431) <
      (-468961268538 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-468961268538 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X2XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (3486679415651837003761 / 2500000000000000000000) (27758139431 / 78758139431) : ℚ) : ℝ) <
      (-468961268538 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP4_arg_eq :
    barrierCase2X2XP4LogArg = barrierComplex (111 / 400) (129341195761 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP4LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP4_arg_regular :
    (barrierCase2X2XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP4LogArg).re := by
  rw [barrierCase2X2XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X2XP4LogArg (0) (2) (17499207420885324369121 / 10000000000000000000000) (129341195761 / 50000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (129341195761 / 50000000000) : ℚ) = (-27750000000 / 129341195761) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761) <
      (78157067239 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (78157067239 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (17499207420885324369121 / 10000000000000000000000) (-27750000000 / 129341195761) : ℚ) : ℝ) <
      (78157067239 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP6_arg_eq :
    barrierCase2X2XP6LogArg = barrierComplex (377571029559 / 1250000000000) (196151029559 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP6LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP6_arg_regular :
    (barrierCase2X2XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP6LogArg).re := by
  rw [barrierCase2X2XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X2XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X2XP6LogArg (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (196151029559 / 62500000000) (-377571029559 / 625000000000)
  have hratio : ((-377571029559 / 625000000000) / (196151029559 / 62500000000) : ℚ) = (-377571029559 / 1961510295590) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590) <
      (108144189988 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (108144189988 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X2XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (3990082522067812425182581 / 3125000000000000000000000) (-377571029559 / 1961510295590) : ℚ) : ℝ) <
      (108144189988 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X2XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X2 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X2XP8_arg_eq :
    barrierCase2X2XP8LogArg = barrierComplex (27588970441 / 1250000000000) (153831029559 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X2XP8LogArg, Case2PointData.X2, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X2XP8_arg_regular :
    (barrierCase2X2XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X2XP8LogArg).re := by
  rw [barrierCase2X2XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X2XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X2XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X2XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X2XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X2XP8LogArg (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (153831029559 / 62500000000) (-27588970441 / 625000000000)
  have hratio : ((-27588970441 / 625000000000) / (153831029559 / 62500000000) : ℚ) = (-27588970441 / 1538310295590) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X2XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X2XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590) <
      (-145548528877 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X2XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X2 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-145548528877 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X2XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X2XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (2367159716808187545182581 / 1562500000000000000000000) (-27588970441 / 1538310295590) : ℚ) : ℝ) <
      (-145548528877 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X2XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
