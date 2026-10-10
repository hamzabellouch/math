import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X8XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X8 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X8XP0_arg_eq :
    barrierCase2X8XP0LogArg = barrierComplex (24909680179 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XP0LogArg, Case2PointData.X8, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XP0_arg_regular :
    (barrierCase2X8XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XP0LogArg).re := by
  rw [barrierCase2X8XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X8XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (1) (0) (620492166620065472041 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X8XP0LogArg (1) (0) (620492166620065472041 / 312500000000000000000) (24909680179 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (24909680179 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (1) (0) (620492166620065472041 / 312500000000000000000) (0 / 1) <
      (-128782453816 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-128782453816 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X8XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (1) (0) (620492166620065472041 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-128782453816 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X8 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X8XP1_arg_eq :
    barrierCase2X8XP1LogArg = barrierComplex (68202865789 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XP1LogArg, Case2PointData.X8, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XP1_arg_regular :
    (barrierCase2X8XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XP1LogArg).re := by
  rw [barrierCase2X8XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X8XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (4651630901832346592521 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X8XP1LogArg (2) (0) (4651630901832346592521 / 3906250000000000000000) (68202865789 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (68202865789 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (4651630901832346592521 / 3906250000000000000000) (0 / 1) <
      (-33427551008 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-33427551008 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X8XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (4651630901832346592521 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-33427551008 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X8 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X8XP2_arg_eq :
    barrierCase2X8XP2LogArg = barrierComplex (51 / 100) (1391118309 / 6250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XP2LogArg, Case2PointData.X8, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XP2_arg_regular :
    (barrierCase2X8XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XP2LogArg).re := by
  rw [barrierCase2X8XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X8XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (12095366399635019481 / 9765625000000000000) (463706103 / 1062500000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X8XP2LogArg (-2) (0) (12095366399635019481 / 9765625000000000000) (51 / 100) (1391118309 / 6250000000)
  have hratio : ((1391118309 / 6250000000) / (51 / 100) : ℚ) = (463706103 / 1062500000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (12095366399635019481 / 9765625000000000000) (463706103 / 1062500000) <
      (257198180351 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (257198180351 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X8XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (12095366399635019481 / 9765625000000000000) (463706103 / 1062500000) : ℚ) : ℝ) <
      (257198180351 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X8 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X8XP4_arg_eq :
    barrierCase2X8XP4LogArg = barrierComplex (111 / 400) (3378430179 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XP4LogArg, Case2PointData.X8, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XP4_arg_regular :
    (barrierCase2X8XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XP4LogArg).re := by
  rw [barrierCase2X8XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X8XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (23446017036877972041 / 19531250000000000000) (-30106607 / 2282393393) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X8XP4LogArg (-3) (1) (23446017036877972041 / 19531250000000000000) (6847180179 / 12500000000) (-90319821 / 12500000000)
  have hratio : ((-90319821 / 12500000000) / (6847180179 / 12500000000) : ℚ) = (-30106607 / 2282393393) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (23446017036877972041 / 19531250000000000000) (-30106607 / 2282393393) <
      (58033623456 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (58033623456 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X8XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (23446017036877972041 / 19531250000000000000) (-30106607 / 2282393393) : ℚ) : ℝ) <
      (58033623456 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X8 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X8XP6_arg_eq :
    barrierCase2X8XP6LogArg = barrierComplex (29893317301 / 156250000000) (7215817301 / 15625000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XP6LogArg, Case2PointData.X8, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XP6_arg_regular :
    (barrierCase2X8XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XP6LogArg).re := by
  rw [barrierCase2X8XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X8XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (1) (6100412351399358384701 / 3051757812500000000000) (42264855709 / 102051490311) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X8XP6LogArg (-3) (1) (6100412351399358384701 / 3051757812500000000000) (102051490311 / 156250000000) (42264855709 / 156250000000)
  have hratio : ((42264855709 / 156250000000) / (102051490311 / 156250000000) : ℚ) = (42264855709 / 102051490311) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (1) (6100412351399358384701 / 3051757812500000000000) (42264855709 / 102051490311) <
      (127547169958 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (127547169958 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X8XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (1) (6100412351399358384701 / 3051757812500000000000) (42264855709 / 102051490311) : ℚ) : ℝ) <
      (127547169958 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X8XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X8 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X8XP8_arg_eq :
    barrierCase2X8XP8LogArg = barrierComplex (20751682699 / 156250000000) (1925817301 / 15625000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X8XP8LogArg, Case2PointData.X8, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X8XP8_arg_regular :
    (barrierCase2X8XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X8XP8LogArg).re := by
  rw [barrierCase2X8XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X8XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X8XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X8XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (801509562523068384701 / 762939453125000000000) (-1493509689 / 40009855709) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X8XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X8XP8LogArg (-5) (1) (801509562523068384701 / 762939453125000000000) (40009855709 / 156250000000) (-1493509689 / 156250000000)
  have hratio : ((-1493509689 / 156250000000) / (40009855709 / 156250000000) : ℚ) = (-1493509689 / 40009855709) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X8XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X8XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (801509562523068384701 / 762939453125000000000) (-1493509689 / 40009855709) <
      (-32043778908 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X8XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X8 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-32043778908 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X8XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X8XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (801509562523068384701 / 762939453125000000000) (-1493509689 / 40009855709) : ℚ) : ℝ) <
      (-32043778908 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X8XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
