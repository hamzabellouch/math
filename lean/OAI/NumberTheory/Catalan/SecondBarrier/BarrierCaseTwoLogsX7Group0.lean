import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI


noncomputable section
namespace InternalCatalan

def barrierCase2X7XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X7 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X7XP0_arg_eq :
    barrierCase2X7XP0LogArg = barrierComplex (103702335521 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X7XP0LogArg, Case2PointData.X7, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X7XP0_arg_regular :
    (barrierCase2X7XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X7XP0LogArg).re := by
  rw [barrierCase2X7XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X7XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X7XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X7XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (10754174392510058341441 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X7XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X7XP0LogArg (2) (0) (10754174392510058341441 / 10000000000000000000000) (103702335521 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (103702335521 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X7XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X7XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (10754174392510058341441 / 10000000000000000000000) (0 / 1) <
      (-136248319383 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X7XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-136248319383 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X7XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X7XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (10754174392510058341441 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-136248319383 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X7XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X7XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X7 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X7XP1_arg_eq :
    barrierCase2X7XP1LogArg = barrierComplex (284046162911 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X7XP1LogArg, Case2PointData.X7, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X7XP1_arg_regular :
    (barrierCase2X7XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X7XP1LogArg).re := by
  rw [barrierCase2X7XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X7XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X7XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X7XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (80682222664462351993921 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X7XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X7XP1LogArg (2) (0) (80682222664462351993921 / 62500000000000000000000) (284046162911 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (284046162911 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X7XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X7XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (80682222664462351993921 / 62500000000000000000000) (0 / 1) <
      (-35155998255 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X7XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-35155998255 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X7XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X7XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (80682222664462351993921 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-35155998255 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X7XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X7XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X7 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X7XP2_arg_eq :
    barrierCase2X7XP2LogArg = barrierComplex (51 / 100) (7237726391 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X7XP2LogArg, Case2PointData.X7, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X7XP2_arg_regular :
    (barrierCase2X7XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X7XP2LogArg).re := by
  rw [barrierCase2X7XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X7XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X7XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X7XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (214947183310977884881 / 156250000000000000000) (-5512273609 / 19987726391) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X7XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X7XP2LogArg (-2) (1) (214947183310977884881 / 156250000000000000000) (19987726391 / 25000000000) (-5512273609 / 25000000000)
  have hratio : ((-5512273609 / 25000000000) / (19987726391 / 25000000000) : ℚ) = (-5512273609 / 19987726391) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X7XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X7XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (214947183310977884881 / 156250000000000000000) (-5512273609 / 19987726391) <
      (188971660183 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X7XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (188971660183 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X7XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X7XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (1) (214947183310977884881 / 156250000000000000000) (-5512273609 / 19987726391) : ℚ) : ℝ) <
      (188971660183 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X7XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X7XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X7 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X7XP4_arg_eq :
    barrierCase2X7XP4LogArg = barrierComplex (111 / 400) (17577335521 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X7XP4LogArg, Case2PointData.X7, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X7XP4_arg_regular :
    (barrierCase2X7XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X7XP4LogArg).re := by
  rw [barrierCase2X7XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X7XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X7XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X7XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (501478349017808341441 / 312500000000000000000) (3702335521 / 31452335521) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X7XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X7XP4LogArg (-3) (1) (501478349017808341441 / 312500000000000000000) (31452335521 / 50000000000) (3702335521 / 50000000000)
  have hratio : ((3702335521 / 50000000000) / (31452335521 / 50000000000) : ℚ) = (3702335521 / 31452335521) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X7XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X7XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (501478349017808341441 / 312500000000000000000) (3702335521 / 31452335521) <
      (64071312829 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X7XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (64071312829 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X7XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X7XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (1) (501478349017808341441 / 312500000000000000000) (3702335521 / 31452335521) : ℚ) : ℝ) <
      (64071312829 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X7XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X7XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X7 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X7XP6_arg_eq :
    barrierCase2X7XP6LogArg = barrierComplex (125071100999 / 625000000000) (34361100999 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X7XP6LogArg, Case2PointData.X7, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X7XP6_arg_regular :
    (barrierCase2X7XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X7XP6LogArg).re := by
  rw [barrierCase2X7XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X7XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X7XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X7XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-2) (1) (133711306491449938598101 / 97656250000000000000000) (218539908991 / 468682110989) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X7XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X7XP6LogArg (-2) (1) (133711306491449938598101 / 97656250000000000000000) (468682110989 / 625000000000) (218539908991 / 625000000000)
  have hratio : ((218539908991 / 625000000000) / (468682110989 / 625000000000) : ℚ) = (218539908991 / 468682110989) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X7XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X7XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-2) (1) (133711306491449938598101 / 97656250000000000000000) (218539908991 / 468682110989) <
      (126369336272 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X7XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (126369336272 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X7XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X7XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-2) (1) (133711306491449938598101 / 97656250000000000000000) (218539908991 / 468682110989) : ℚ) : ℝ) <
      (126369336272 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X7XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X7XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X7 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X7XP8_arg_eq :
    barrierCase2X7XP8LogArg = barrierComplex (77508899001 / 625000000000) (13201100999 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X7XP8LogArg, Case2PointData.X7, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X7XP8_arg_regular :
    (barrierCase2X7XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X7XP8LogArg).re := by
  rw [barrierCase2X7XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X7XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X7XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X7XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (23434536182927098598101 / 12207031250000000000000) (54502110989 / 209519908991) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X7XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X7XP8LogArg (-5) (1) (23434536182927098598101 / 12207031250000000000000) (209519908991 / 625000000000) (54502110989 / 625000000000)
  have hratio : ((54502110989 / 625000000000) / (209519908991 / 625000000000) : ℚ) = (54502110989 / 209519908991) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X7XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X7XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (23434536182927098598101 / 12207031250000000000000) (54502110989 / 209519908991) <
      (-64919059108 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X7XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X7 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-64919059108 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X7XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X7XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-5) (1) (23434536182927098598101 / 12207031250000000000000) (54502110989 / 209519908991) : ℚ) : ℝ) <
      (-64919059108 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X7XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
