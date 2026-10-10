import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X4XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP0_arg_eq :
    barrierCase2X4XP0LogArg = barrierComplex (52081937821 / 20000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP0LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP0_arg_regular :
    (barrierCase2X4XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP0LogArg).re := by
  rw [barrierCase2X4XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X4XP0LogArg (2) (0) (2712528247190510228041 / 1600000000000000000000) (52081937821 / 20000000000) (0 / 1)
  have hratio : ((0 / 1) / (52081937821 / 20000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1) <
      (-178754020753 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-178754020753 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (2712528247190510228041 / 1600000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-178754020753 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP1_arg_eq :
    barrierCase2X4XP1LogArg = barrierComplex (142927122211 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP1LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP1_arg_regular :
    (barrierCase2X4XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP1LogArg).re := by
  rw [barrierCase2X4XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X4XP1LogArg (3) (0) (20428162263518129528521 / 20000000000000000000000) (142927122211 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (142927122211 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1) <
      (-44985046020 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-44985046020 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (20428162263518129528521 / 20000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-44985046020 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP2_arg_eq :
    barrierCase2X4XP2LogArg = barrierComplex (51 / 100) (7260209691 / 10000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP2LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP2_arg_regular :
    (barrierCase2X4XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP2LogArg).re := by
  rw [barrierCase2X4XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X4XP2LogArg (-1) (1) (78720644757290315481 / 50000000000000000000) (12360209691 / 10000000000) (2160209691 / 10000000000)
  have hratio : ((2160209691 / 10000000000) / (12360209691 / 10000000000) : ℚ) = (720069897 / 4120069897) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897) <
      (-226519279066 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-226519279066 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (78720644757290315481 / 50000000000000000000) (720069897 / 4120069897) : ℚ) : ℝ) <
      (-226519279066 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP4_arg_eq :
    barrierCase2X4XP4LogArg = barrierComplex (111 / 400) (17631937821 / 20000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP4LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP4_arg_regular :
    (barrierCase2X4XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP4LogArg).re := by
  rw [barrierCase2X4XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X4XP4LogArg (-1) (2) (341687731323610228041 / 200000000000000000000) (17631937821 / 10000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (17631937821 / 10000000000) : ℚ) = (-1850000000 / 5877312607) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607) <
      (76954522124 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (76954522124 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (2) (341687731323610228041 / 200000000000000000000) (-1850000000 / 5877312607) : ℚ) : ℝ) <
      (76954522124 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP6_arg_eq :
    barrierCase2X4XP6LogArg = barrierComplex (64370974699 / 250000000000) (28086974699 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP6LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP6_arg_regular :
    (barrierCase2X4XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP6LogArg).re := by
  rw [barrierCase2X4XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X4XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X4XP6LogArg (0) (2) (83031437157925912200701 / 62500000000000000000000) (28086974699 / 12500000000) (-64370974699 / 125000000000)
  have hratio : ((-64370974699 / 125000000000) / (28086974699 / 12500000000) : ℚ) = (-64370974699 / 280869746990) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990) <
      (115547972121 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (115547972121 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X4XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (83031437157925912200701 / 62500000000000000000000) (-64370974699 / 280869746990) : ℚ) : ℝ) <
      (115547972121 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X4XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X4 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X4XP8_arg_eq :
    barrierCase2X4XP8LogArg = barrierComplex (16661025301 / 250000000000) (19622974699 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X4XP8LogArg, Case2PointData.X4, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X4XP8_arg_regular :
    (barrierCase2X4XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X4XP8LogArg).re := by
  rw [barrierCase2X4XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X4XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X4XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X4XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X4XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X4XP8LogArg (-1) (2) (38783703367839976200701 / 31250000000000000000000) (19622974699 / 12500000000) (-16661025301 / 125000000000)
  have hratio : ((-16661025301 / 125000000000) / (19622974699 / 12500000000) : ℚ) = (-16661025301 / 196229746990) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X4XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X4XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990) <
      (-130081594412 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X4XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X4 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-130081594412 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X4XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X4XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (2) (38783703367839976200701 / 31250000000000000000000) (-16661025301 / 196229746990) : ℚ) : ℝ) <
      (-130081594412 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X4XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
