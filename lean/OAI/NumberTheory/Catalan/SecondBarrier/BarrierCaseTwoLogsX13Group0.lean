import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X13XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X13 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X13XP0_arg_eq :
    barrierCase2X13XP0LogArg = barrierComplex (72776978617 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X13XP0LogArg, Case2PointData.X13, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X13XP0_arg_regular :
    (barrierCase2X13XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X13XP0LogArg).re := by
  rw [barrierCase2X13XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X13XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X13XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X13XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-1) (0) (5296488616619275232689 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X13XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X13XP0LogArg (-1) (0) (5296488616619275232689 / 5000000000000000000000) (72776978617 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (72776978617 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X13XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X13XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-1) (0) (5296488616619275232689 / 5000000000000000000000) (0 / 1) <
      (59349692830 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X13XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (59349692830 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X13XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X13XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-1) (0) (5296488616619275232689 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (59349692830 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X13XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X13XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X13 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X13XP1_arg_eq :
    barrierCase2X13XP1LogArg = barrierComplex (195886352647 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X13XP1LogArg, Case2PointData.X13, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X13XP1_arg_regular :
    (barrierCase2X13XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X13XP1LogArg).re := by
  rw [barrierCase2X13XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X13XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X13XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X13XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-1) (0) (38371463153344843906609 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X13XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X13XP1LogArg (-1) (0) (38371463153344843906609 / 31250000000000000000000) (195886352647 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (195886352647 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X13XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X13XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-1) (0) (38371463153344843906609 / 31250000000000000000000) (0 / 1) <
      (10447405634 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X13XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (10447405634 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X13XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X13XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-1) (0) (38371463153344843906609 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (10447405634 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X13XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X13XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X13 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X13XP2_arg_eq :
    barrierCase2X13XP2LogArg = barrierComplex (51 / 100) (-40959479393 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X13XP2LogArg, Case2PointData.X13, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X13XP2_arg_regular :
    (barrierCase2X13XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X13XP2LogArg).re := by
  rw [barrierCase2X13XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X13XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X13XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X13XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (2327928952145591648449 / 1250000000000000000000) (-15459479393 / 66459479393) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X13XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X13XP2LogArg (-1) (-1) (2327928952145591648449 / 1250000000000000000000) (66459479393 / 50000000000) (-15459479393 / 50000000000)
  have hratio : ((-15459479393 / 50000000000) / (66459479393 / 50000000000) : ℚ) = (-15459479393 / 66459479393) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X13XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X13XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (2327928952145591648449 / 1250000000000000000000) (-15459479393 / 66459479393) <
      (347158393557 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X13XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (347158393557 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X13XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X13XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (-1) (2327928952145591648449 / 1250000000000000000000) (-15459479393 / 66459479393) : ℚ) : ℝ) <
      (347158393557 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X13XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X13XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X13 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X13XP4_arg_eq :
    barrierCase2X13XP4LogArg = barrierComplex (111 / 400) (-99473021383 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X13XP4LogArg, Case2PointData.X13, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X13XP4_arg_regular :
    (barrierCase2X13XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X13XP4LogArg).re := by
  rw [barrierCase2X13XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X13XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X13XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X13XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (10664944483062775232689 / 10000000000000000000000) (27750000000 / 99473021383) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X13XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X13XP4LogArg (0) (-2) (10664944483062775232689 / 10000000000000000000000) (99473021383 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (99473021383 / 50000000000) : ℚ) = (27750000000 / 99473021383) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X13XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X13XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (10664944483062775232689 / 10000000000000000000000) (27750000000 / 99473021383) <
      (-78355375634 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X13XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-78355375634 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X13XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X13XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (-2) (10664944483062775232689 / 10000000000000000000000) (27750000000 / 99473021383) : ℚ) : ℝ) <
      (-78355375634 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X13XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X13XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X13 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X13XP6_arg_eq :
    barrierCase2X13XP6LogArg = barrierComplex (67998853423 / 1250000000000) (-113421146577 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X13XP6LogArg, Case2PointData.X13, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X13XP6_arg_regular :
    (barrierCase2X13XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X13XP6LogArg).re := by
  rw [barrierCase2X13XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X13XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X13XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X13XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (-2) (1291059493150974520509829 / 781250000000000000000000) (67998853423 / 1134211465770) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X13XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X13XP6LogArg (-1) (-2) (1291059493150974520509829 / 781250000000000000000000) (113421146577 / 62500000000) (67998853423 / 625000000000)
  have hratio : ((67998853423 / 625000000000) / (113421146577 / 62500000000) : ℚ) = (67998853423 / 1134211465770) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X13XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X13XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (-2) (1291059493150974520509829 / 781250000000000000000000) (67998853423 / 1134211465770) <
      (-131820156918 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X13XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-131820156918 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X13XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X13XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (-2) (1291059493150974520509829 / 781250000000000000000000) (67998853423 / 1134211465770) : ℚ) : ℝ) <
      (-131820156918 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X13XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X13XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X13 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X13XP8_arg_eq :
    barrierCase2X13XP8LogArg = barrierComplex (337161146577 / 1250000000000) (-155741146577 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X13XP8LogArg, Case2PointData.X13, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X13XP8_arg_regular :
    (barrierCase2X13XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X13XP8LogArg).re := by
  rw [barrierCase2X13XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X13XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X13XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X13XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (2539208112472977160509829 / 1562500000000000000000000) (337161146577 / 1557411465770) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X13XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X13XP8LogArg (0) (-2) (2539208112472977160509829 / 1562500000000000000000000) (155741146577 / 62500000000) (337161146577 / 625000000000)
  have hratio : ((337161146577 / 625000000000) / (155741146577 / 62500000000) : ℚ) = (337161146577 / 1557411465770) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X13XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X13XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (2539208112472977160509829 / 1562500000000000000000000) (337161146577 / 1557411465770) <
      (118311273198 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X13XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X13 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (118311273198 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X13XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X13XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (2539208112472977160509829 / 1562500000000000000000000) (337161146577 / 1557411465770) : ℚ) : ℝ) <
      (118311273198 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X13XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
