import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X1XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP0_arg_eq :
    barrierCase2X1XP0LogArg = barrierComplex (81067349681 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP0LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP0_arg_regular :
    (barrierCase2X1XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP0LogArg).re := by
  rw [barrierCase2X1XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X1XP0LogArg (3) (0) (6571915184301530801761 / 5000000000000000000000) (81067349681 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (81067349681 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1) <
      (-219715931992 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-219715931992 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (6571915184301530801761 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-219715931992 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP1_arg_eq :
    barrierCase2X1XP1LogArg = barrierComplex (222797231471 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP1LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP1_arg_regular :
    (barrierCase2X1XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP1LogArg).re := by
  rw [barrierCase2X1XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X1XP1LogArg (3) (0) (49638606351142352823841 / 31250000000000000000000) (222797231471 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (222797231471 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1) <
      (-54441250138 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-54441250138 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (49638606351142352823841 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-54441250138 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP2_arg_eq :
    barrierCase2X1XP2LogArg = barrierComplex (51 / 100) (15649055751 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP2LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP2_arg_regular :
    (barrierCase2X1XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP2LogArg).re := by
  rw [barrierCase2X1XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X1XP2LogArg (0) (1) (285533570897906174001 / 156250000000000000000) (22024055751 / 12500000000) (9274055751 / 12500000000)
  have hratio : ((9274055751 / 12500000000) / (22024055751 / 12500000000) : ℚ) = (3091351917 / 7341351917) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917) <
      (-577565314512 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-577565314512 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (285533570897906174001 / 156250000000000000000) (3091351917 / 7341351917) : ℚ) : ℝ) <
      (-577565314512 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP4_arg_eq :
    barrierCase2X1XP4LogArg = barrierComplex (111 / 400) (38004849681 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP4LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP4_arg_regular :
    (barrierCase2X1XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP4LogArg).re := by
  rw [barrierCase2X1XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X1XP4LogArg (1) (2) (1492497505525405801761 / 1250000000000000000000) (38004849681 / 12500000000) (-111 / 200)
  have hratio : ((-111 / 200) / (38004849681 / 12500000000) : ℚ) = (-2312500000 / 12668283227) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227) <
      (78090797977 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (78090797977 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1492497505525405801761 / 1250000000000000000000) (-2312500000 / 12668283227) : ℚ) : ℝ) <
      (78090797977 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP6_arg_eq :
    barrierCase2X1XP6LogArg = barrierComplex (102063326039 / 312500000000) (56708326039 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP6LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP6_arg_regular :
    (barrierCase2X1XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP6LogArg).re := by
  rw [barrierCase2X1XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X1XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X1XP6LogArg (1) (2) (332000346736695758381621 / 195312500000000000000000) (56708326039 / 15625000000) (-102063326039 / 156250000000)
  have hratio : ((-102063326039 / 156250000000) / (56708326039 / 15625000000) : ℚ) = (-102063326039 / 567083260390) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390) <
      (104608101086 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (104608101086 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X1XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (332000346736695758381621 / 195312500000000000000000) (-102063326039 / 567083260390) : ℚ) : ℝ) <
      (104608101086 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X1XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X1 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X1XP8_arg_eq :
    barrierCase2X1XP8LogArg = barrierComplex (-773326039 / 312500000000) (46128326039 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X1XP8LogArg, Case2PointData.X1, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X1XP8_arg_regular :
    (barrierCase2X1XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X1XP8LogArg).re := by
  rw [barrierCase2X1XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X1XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X1XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X1XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X1XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X1XP8LogArg (1) (2) (212782844349191138381621 / 195312500000000000000000) (46128326039 / 15625000000) (773326039 / 156250000000)
  have hratio : ((773326039 / 156250000000) / (46128326039 / 15625000000) : ℚ) = (773326039 / 461283260390) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X1XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X1XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390) <
      (-151157166207 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X1XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X1 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-151157166207 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X1XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X1XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (212782844349191138381621 / 195312500000000000000000) (773326039 / 461283260390) : ℚ) : ℝ) <
      (-151157166207 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X1XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
