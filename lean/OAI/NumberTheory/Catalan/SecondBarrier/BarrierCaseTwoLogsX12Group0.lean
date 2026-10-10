import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X12XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X12 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X12XP0_arg_eq :
    barrierCase2X12XP0LogArg = barrierComplex (97770969741 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XP0LogArg, Case2PointData.X12, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XP0_arg_regular :
    (barrierCase2X12XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XP0LogArg).re := by
  rw [barrierCase2X12XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X12XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-1) (0) (9559162524095537607081 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X12XP0LogArg (-1) (0) (9559162524095537607081 / 5000000000000000000000) (97770969741 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (97770969741 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-1) (0) (9559162524095537607081 / 5000000000000000000000) (0 / 1) <
      (4210238457 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (4210238457 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X12XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-1) (0) (9559162524095537607081 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (4210238457 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X12 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X12XP1_arg_eq :
    barrierCase2X12XP1LogArg = barrierComplex (264987386931 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XP1LogArg, Case2PointData.X12, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XP1_arg_regular :
    (barrierCase2X12XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XP1LogArg).re := by
  rw [barrierCase2X12XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X12XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (70218315232519509598761 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X12XP1LogArg (0) (0) (70218315232519509598761 / 62500000000000000000000) (264987386931 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (264987386931 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (70218315232519509598761 / 62500000000000000000000) (0 / 1) <
      (-2493629207 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-2493629207 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X12XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (70218315232519509598761 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-2493629207 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X12 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X12XP2_arg_eq :
    barrierCase2X12XP2LogArg = barrierComplex (51 / 100) (-30667835989 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XP2LogArg, Case2PointData.X12, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XP2_arg_regular :
    (barrierCase2X12XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XP2LogArg).re := by
  rw [barrierCase2X12XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X12XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (1590766164248203608121 / 1250000000000000000000) (-5167835989 / 56167835989) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X12XP2LogArg (-1) (-1) (1590766164248203608121 / 1250000000000000000000) (56167835989 / 50000000000) (-5167835989 / 50000000000)
  have hratio : ((-5167835989 / 50000000000) / (56167835989 / 50000000000) : ℚ) = (-5167835989 / 56167835989) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (1590766164248203608121 / 1250000000000000000000) (-5167835989 / 56167835989) <
      (429689194962 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (429689194962 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X12XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (1590766164248203608121 / 1250000000000000000000) (-5167835989 / 56167835989) : ℚ) : ℝ) <
      (429689194962 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X12 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X12XP4_arg_eq :
    barrierCase2X12XP4LogArg = barrierComplex (111 / 400) (-74479030259 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XP4LogArg, Case2PointData.X12, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XP4_arg_regular :
    (barrierCase2X12XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XP4LogArg).re := by
  rw [barrierCase2X12XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X12XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (-1) (6317188448321037607081 / 5000000000000000000000) (-46729030259 / 102229030259) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X12XP4LogArg (-1) (-1) (6317188448321037607081 / 5000000000000000000000) (102229030259 / 100000000000) (-46729030259 / 100000000000)
  have hratio : ((-46729030259 / 100000000000) / (102229030259 / 100000000000) : ℚ) = (-46729030259 / 102229030259) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (-1) (6317188448321037607081 / 5000000000000000000000) (-46729030259 / 102229030259) <
      (-70052073413 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-70052073413 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X12XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (-1) (6317188448321037607081 / 5000000000000000000000) (-46729030259 / 102229030259) : ℚ) : ℝ) <
      (-70052073413 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X12 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X12XP6_arg_eq :
    barrierCase2X12XP6LogArg = barrierComplex (101814253179 / 1250000000000) (-79605746821 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XP6LogArg, Case2PointData.X12, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XP6_arg_regular :
    (barrierCase2X12XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XP6LogArg).re := by
  rw [barrierCase2X12XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X12XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-2) (-2) (644073634843312672210141 / 390625000000000000000000) (101814253179 / 796057468210) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X12XP6LogArg (-2) (-2) (644073634843312672210141 / 390625000000000000000000) (79605746821 / 62500000000) (101814253179 / 625000000000)
  have hratio : ((101814253179 / 625000000000) / (79605746821 / 62500000000) : ℚ) = (101814253179 / 796057468210) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-2) (-2) (644073634843312672210141 / 390625000000000000000000) (101814253179 / 796057468210) <
      (-114592472628 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-114592472628 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X12XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-2) (-2) (644073634843312672210141 / 390625000000000000000000) (101814253179 / 796057468210) : ℚ) : ℝ) <
      (-114592472628 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X12XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X12 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X12XP8_arg_eq :
    barrierCase2X12XP8LogArg = barrierComplex (303345746821 / 1250000000000) (-121925746821 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X12XP8LogArg, Case2PointData.X12, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X12XP8_arg_regular :
    (barrierCase2X12XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X12XP8LogArg).re := by
  rw [barrierCase2X12XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X12XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X12XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X12XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (1578607415900249392210141 / 1562500000000000000000000) (303345746821 / 1219257468210) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X12XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X12XP8LogArg (0) (-2) (1578607415900249392210141 / 1562500000000000000000000) (121925746821 / 62500000000) (303345746821 / 625000000000)
  have hratio : ((303345746821 / 625000000000) / (121925746821 / 62500000000) : ℚ) = (303345746821 / 1219257468210) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X12XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X12XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (1578607415900249392210141 / 1562500000000000000000000) (303345746821 / 1219257468210) <
      (120529011305 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X12XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (120529011305 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X12XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X12XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (1578607415900249392210141 / 1562500000000000000000000) (303345746821 / 1219257468210) : ℚ) : ℝ) <
      (120529011305 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X12XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
