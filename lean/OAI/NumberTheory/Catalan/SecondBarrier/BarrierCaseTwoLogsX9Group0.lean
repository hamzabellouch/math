import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X9XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X9 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X9XP0_arg_eq :
    barrierCase2X9XP0LogArg = barrierComplex (73103441473 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XP0LogArg, Case2PointData.X9, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XP0_arg_regular :
    (barrierCase2X9XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XP0LogArg).re := by
  rw [barrierCase2X9XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X9XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (1) (0) (5344113155196336409729 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X9XP0LogArg (1) (0) (5344113155196336409729 / 5000000000000000000000) (73103441473 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (73103441473 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (1) (0) (5344113155196336409729 / 5000000000000000000000) (0 / 1) <
      (-70944675408 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-70944675408 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X9XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (1) (0) (5344113155196336409729 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-70944675408 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X9 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X9XP1_arg_eq :
    barrierCase2X9XP1LogArg = barrierComplex (199449220543 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XP1LogArg, Case2PointData.X9, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XP1_arg_regular :
    (barrierCase2X9XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XP1LogArg).re := by
  rw [barrierCase2X9XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X9XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (1) (0) (39779991575210253214849 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X9XP1LogArg (1) (0) (39779991575210253214849 / 31250000000000000000000) (199449220543 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (199449220543 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (1) (0) (39779991575210253214849 / 31250000000000000000000) (0 / 1) <
      (-20012227414 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-20012227414 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X9XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (1) (0) (39779991575210253214849 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-20012227414 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X9 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X9XP2_arg_eq :
    barrierCase2X9XP2LogArg = barrierComplex (51 / 100) (-5361818217 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XP2LogArg, Case2PointData.X9, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XP2_arg_regular :
    (barrierCase2X9XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XP2LogArg).re := by
  rw [barrierCase2X9XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X9XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (191311594592153059089 / 156250000000000000000) (-1787272739 / 4250000000) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X9XP2LogArg (-2) (0) (191311594592153059089 / 156250000000000000000) (51 / 100) (-5361818217 / 25000000000)
  have hratio : ((-5361818217 / 25000000000) / (51 / 100) : ℚ) = (-1787272739 / 4250000000) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (191311594592153059089 / 156250000000000000000) (-1787272739 / 4250000000) <
      (519333423834 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (519333423834 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X9XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (0) (191311594592153059089 / 156250000000000000000) (-1787272739 / 4250000000) : ℚ) : ℝ) <
      (519333423834 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X9 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X9XP4_arg_eq :
    barrierCase2X9XP4LogArg = barrierComplex (111 / 400) (-13021558527 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XP4LogArg, Case2PointData.X9, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XP4_arg_regular :
    (barrierCase2X9XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XP4LogArg).re := by
  rw [barrierCase2X9XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X9XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (362076611472086409729 / 312500000000000000000) (284480491 / 8965519509) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X9XP4LogArg (-3) (-1) (362076611472086409729 / 312500000000000000000) (26896558527 / 50000000000) (853441473 / 50000000000)
  have hratio : ((853441473 / 50000000000) / (26896558527 / 50000000000) : ℚ) = (284480491 / 8965519509) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (362076611472086409729 / 312500000000000000000) (284480491 / 8965519509) <
      (-33341712769 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-33341712769 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X9XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (362076611472086409729 / 312500000000000000000) (284480491 / 8965519509) : ℚ) : ℝ) <
      (-33341712769 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X9 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X9XP6_arg_eq :
    barrierCase2X9XP6LogArg = barrierComplex (83672597287 / 625000000000) (-7037402713 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XP6LogArg, Case2PointData.X9, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XP6_arg_regular :
    (barrierCase2X9XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XP6LogArg).re := by
  rw [barrierCase2X9XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X9XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-6) (-1) (11953607231246455797269 / 6103515625000000000000) (13298570157 / 154046624417) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X9XP6LogArg (-6) (-1) (11953607231246455797269 / 6103515625000000000000) (154046624417 / 625000000000) (13298570157 / 625000000000)
  have hratio : ((13298570157 / 625000000000) / (154046624417 / 625000000000) : ℚ) = (13298570157 / 154046624417) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-6) (-1) (11953607231246455797269 / 6103515625000000000000) (13298570157 / 154046624417) <
      (-6194380483 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-6194380483 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X9XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-6) (-1) (11953607231246455797269 / 6103515625000000000000) (13298570157 / 154046624417) : ℚ) : ℝ) <
      (-6194380483 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X9XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X9 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X9XP8_arg_eq :
    barrierCase2X9XP8LogArg = barrierComplex (118907402713 / 625000000000) (-28197402713 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X9XP8LogArg, Case2PointData.X9, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X9XP8_arg_regular :
    (barrierCase2X9XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X9XP8LogArg).re := by
  rw [barrierCase2X9XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X9XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X9XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X9XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-3) (-1) (93648322395861535797269 / 48828125000000000000000) (-163066624417 / 400881429843) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X9XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X9XP8LogArg (-3) (-1) (93648322395861535797269 / 48828125000000000000000) (400881429843 / 625000000000) (-163066624417 / 625000000000)
  have hratio : ((-163066624417 / 625000000000) / (400881429843 / 625000000000) : ℚ) = (-163066624417 / 400881429843) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X9XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X9XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-3) (-1) (93648322395861535797269 / 48828125000000000000000) (-163066624417 / 400881429843) <
      (121560737504 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X9XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (121560737504 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X9XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X9XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-3) (-1) (93648322395861535797269 / 48828125000000000000000) (-163066624417 / 400881429843) : ℚ) : ℝ) <
      (121560737504 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X9XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
