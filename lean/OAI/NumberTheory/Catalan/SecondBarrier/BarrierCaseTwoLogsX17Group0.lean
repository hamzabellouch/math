import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X17XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X17 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X17XP0_arg_eq :
    barrierCase2X17XP0LogArg = barrierComplex (7183634277 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XP0LogArg, Case2PointData.X17, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XP0_arg_regular :
    (barrierCase2X17XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XP0LogArg).re := by
  rw [barrierCase2X17XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X17XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-8) (0) (51604601425689312729 / 39062500000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X17XP0LogArg (-8) (0) (51604601425689312729 / 39062500000000000000) (7183634277 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (7183634277 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-8) (0) (51604601425689312729 / 39062500000000000000) (0 / 1) <
      (491831008995 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (491831008995 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X17XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-8) (0) (51604601425689312729 / 39062500000000000000) (0 / 1) : ℚ) : ℝ) <
      (491831008995 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X17 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X17XP1_arg_eq :
    barrierCase2X17XP1LogArg = barrierComplex (14540047707 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XP1LogArg, Case2PointData.X17, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XP1_arg_regular :
    (barrierCase2X17XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XP1LogArg).re := by
  rw [barrierCase2X17XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X17XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-9) (0) (211412987321835957849 / 122070312500000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X17XP1LogArg (-9) (0) (211412987321835957849 / 122070312500000000000) (14540047707 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (14540047707 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-9) (0) (211412987321835957849 / 122070312500000000000) (0 / 1) <
      (121832766894 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (121832766894 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X17XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-9) (0) (211412987321835957849 / 122070312500000000000) (0 / 1) : ℚ) : ℝ) <
      (121832766894 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X17 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X17XP2_arg_eq :
    barrierCase2X17XP2LogArg = barrierComplex (51 / 100) (-67968503533 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XP2LogArg, Case2PointData.X17, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XP2_arg_regular :
    (barrierCase2X17XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XP2LogArg).re := by
  rw [barrierCase2X17XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X17XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (-1) (5269967472515433482089 / 5000000000000000000000) (-42468503533 / 93468503533) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X17XP2LogArg (1) (-1) (5269967472515433482089 / 5000000000000000000000) (93468503533 / 50000000000) (-42468503533 / 50000000000)
  have hratio : ((-42468503533 / 50000000000) / (93468503533 / 50000000000) : ℚ) = (-42468503533 / 93468503533) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (-1) (5269967472515433482089 / 5000000000000000000000) (-42468503533 / 93468503533) <
      (139550994281 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (139550994281 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X17XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (-1) (5269967472515433482089 / 5000000000000000000000) (-42468503533 / 93468503533) : ℚ) : ℝ) <
      (139550994281 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X17 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X17XP4_arg_eq :
    barrierCase2X17XP4LogArg = barrierComplex (111 / 400) (-165066365723 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XP4LogArg, Case2PointData.X17, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XP4_arg_regular :
    (barrierCase2X17XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XP4LogArg).re := by
  rw [barrierCase2X17XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X17XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (28016967592999189312729 / 20000000000000000000000) (27750000000 / 165066365723) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X17XP4LogArg (1) (-2) (28016967592999189312729 / 20000000000000000000000) (165066365723 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (165066365723 / 50000000000) : ℚ) = (27750000000 / 165066365723) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (28016967592999189312729 / 20000000000000000000000) (27750000000 / 165066365723) <
      (-90635905951 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-90635905951 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X17XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (-2) (28016967592999189312729 / 20000000000000000000000) (27750000000 / 165066365723) : ℚ) : ℝ) <
      (-90635905951 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X17 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X17XP6_arg_eq :
    barrierCase2X17XP6LogArg = barrierComplex (-20745083037 / 1250000000000) (-202165083037 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XP6LogArg, Case2PointData.X17, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XP6_arg_regular :
    (barrierCase2X17XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XP6LogArg).re := by
  rw [barrierCase2X17XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X17XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (4087502438405922539480269 / 3125000000000000000000000) (-20745083037 / 2021650830370) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X17XP6LogArg (1) (-2) (4087502438405922539480269 / 3125000000000000000000000) (202165083037 / 62500000000) (-20745083037 / 625000000000)
  have hratio : ((-20745083037 / 625000000000) / (202165083037 / 62500000000) : ℚ) = (-20745083037 / 2021650830370) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (4087502438405922539480269 / 3125000000000000000000000) (-20745083037 / 2021650830370) <
      (-156671478776 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-156671478776 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X17XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (-2) (4087502438405922539480269 / 3125000000000000000000000) (-20745083037 / 2021650830370) : ℚ) : ℝ) <
      (-156671478776 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X17XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X17 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X17XP8_arg_eq :
    barrierCase2X17XP8LogArg = barrierComplex (425905083037 / 1250000000000) (-244485083037 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X17XP8LogArg, Case2PointData.X17, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X17XP8_arg_regular :
    (barrierCase2X17XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X17XP8LogArg).re := by
  rw [barrierCase2X17XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X17XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X17XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X17XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (6158690722517632379480269 / 3125000000000000000000000) (425905083037 / 2444850830370) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X17XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X17XP8LogArg (1) (-2) (6158690722517632379480269 / 3125000000000000000000000) (244485083037 / 62500000000) (425905083037 / 625000000000)
  have hratio : ((425905083037 / 625000000000) / (244485083037 / 62500000000) : ℚ) = (425905083037 / 2444850830370) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X17XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X17XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (6158690722517632379480269 / 3125000000000000000000000) (425905083037 / 2444850830370) <
      (112685959762 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X17XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X17 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (112685959762 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X17XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X17XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (-2) (6158690722517632379480269 / 3125000000000000000000000) (425905083037 / 2444850830370) : ℚ) : ℝ) <
      (112685959762 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X17XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
