import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X6XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X6 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X6XP0_arg_eq :
    barrierCase2X6XP0LogArg = barrierComplex (112549856491 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XP0LogArg, Case2PointData.X6, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XP0_arg_regular :
    (barrierCase2X6XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XP0LogArg).re := by
  rw [barrierCase2X6XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X6XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (12667470196144694833081 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X6XP0LogArg (2) (0) (12667470196144694833081 / 10000000000000000000000) (112549856491 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (112549856491 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (12667470196144694833081 / 10000000000000000000000) (0 / 1) <
      (-151539409866 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-151539409866 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X6XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (12667470196144694833081 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-151539409866 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X6 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X6XP1_arg_eq :
    barrierCase2X6XP1LogArg = barrierComplex (308506956181 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XP1LogArg, Case2PointData.X6, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XP1_arg_regular :
    (barrierCase2X6XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XP1LogArg).re := by
  rw [barrierCase2X6XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X6XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (95176542012065454104761 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X6XP1LogArg (2) (0) (95176542012065454104761 / 62500000000000000000000) (308506956181 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (308506956181 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (95176542012065454104761 / 62500000000000000000000) (0 / 1) <
      (-38694097535 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-38694097535 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X6XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (95176542012065454104761 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-38694097535 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X6 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X6XP2_arg_eq :
    barrierCase2X6XP2LogArg = barrierComplex (51 / 100) (10880823261 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XP2LogArg, Case2PointData.X6, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XP2_arg_regular :
    (barrierCase2X6XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XP2LogArg).re := by
  rw [barrierCase2X6XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X6XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (280954814837118674121 / 156250000000000000000) (-623058913 / 7876941087) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X6XP2LogArg (-2) (1) (280954814837118674121 / 156250000000000000000) (23630823261 / 25000000000) (-1869176739 / 25000000000)
  have hratio : ((-1869176739 / 25000000000) / (23630823261 / 25000000000) : ℚ) = (-623058913 / 7876941087) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (280954814837118674121 / 156250000000000000000) (-623058913 / 7876941087) <
      (39549843424 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (39549843424 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X6XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (280954814837118674121 / 156250000000000000000) (-623058913 / 7876941087) : ℚ) : ℝ) <
      (39549843424 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X6 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X6XP4_arg_eq :
    barrierCase2X6XP4LogArg = barrierComplex (111 / 400) (26424856491 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XP4LogArg, Case2PointData.X6, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XP4_arg_regular :
    (barrierCase2X6XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XP4LogArg).re := by
  rw [barrierCase2X6XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X6XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (1) (890788665569944833081 / 625000000000000000000) (4183285497 / 13433285497) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X6XP4LogArg (-2) (1) (890788665569944833081 / 625000000000000000000) (40299856491 / 50000000000) (12549856491 / 50000000000)
  have hratio : ((12549856491 / 50000000000) / (40299856491 / 50000000000) : ℚ) = (4183285497 / 13433285497) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (1) (890788665569944833081 / 625000000000000000000) (4183285497 / 13433285497) <
      (71621189177 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (71621189177 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X6XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (1) (890788665569944833081 / 625000000000000000000) (4183285497 / 13433285497) : ℚ) : ℝ) <
      (71621189177 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X6 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X6XP6_arg_eq :
    barrierCase2X6XP6LogArg = barrierComplex (137041276429 / 625000000000) (46331276429 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XP6LogArg, Case2PointData.X6, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XP6_arg_regular :
    (barrierCase2X6XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XP6LogArg).re := by
  rw [barrierCase2X6XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X6XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (233439028999330690196141 / 195312500000000000000000) (-137041276429 / 463312764290) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X6XP6LogArg (-1) (2) (233439028999330690196141 / 195312500000000000000000) (46331276429 / 31250000000) (-137041276429 / 312500000000)
  have hratio : ((-137041276429 / 312500000000) / (46331276429 / 31250000000) : ℚ) = (-137041276429 / 463312764290) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (233439028999330690196141 / 195312500000000000000000) (-137041276429 / 463312764290) <
      (122871973672 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (122871973672 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X6XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (233439028999330690196141 / 195312500000000000000000) (-137041276429 / 463312764290) : ℚ) : ℝ) <
      (122871973672 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X6XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X6 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X6XP8_arg_eq :
    barrierCase2X6XP8LogArg = barrierComplex (65538723571 / 625000000000) (25171276429 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X6XP8LogArg, Case2PointData.X6, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X6XP8_arg_regular :
    (barrierCase2X6XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X6XP8LogArg).re := by
  rw [barrierCase2X6XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X6XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X6XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X6XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-3) (2) (67654639993829050196141 / 48828125000000000000000) (-65538723571 / 251712764290) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X6XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X6XP8LogArg (-3) (2) (67654639993829050196141 / 48828125000000000000000) (25171276429 / 31250000000) (-65538723571 / 312500000000)
  have hratio : ((-65538723571 / 312500000000) / (25171276429 / 31250000000) : ℚ) = (-65538723571 / 251712764290) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X6XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X6XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-3) (2) (67654639993829050196141 / 48828125000000000000000) (-65538723571 / 251712764290) <
      (-101190156240 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X6XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X6 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-101190156240 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X6XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X6XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-3) (2) (67654639993829050196141 / 48828125000000000000000) (-65538723571 / 251712764290) : ℚ) : ℝ) <
      (-101190156240 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X6XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
