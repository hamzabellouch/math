import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X0XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP0_arg_eq :
    barrierCase2X0XP0LogArg = barrierComplex (83867213879 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP0LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP0_arg_regular :
    (barrierCase2X0XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP0LogArg).re := by
  rw [barrierCase2X0XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X0XP0LogArg (3) (0) (7033709563825930226641 / 5000000000000000000000) (83867213879 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (83867213879 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1) <
      (-226057576541 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-226057576541 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (3) (0) (7033709563825930226641 / 5000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-226057576541 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP1_arg_eq :
    barrierCase2X0XP1LogArg = barrierComplex (230538032489 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP1LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP1_arg_regular :
    (barrierCase2X0XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP1LogArg).re := by
  rw [barrierCase2X0XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X0XP1LogArg (3) (0) (53147784423899219535121 / 31250000000000000000000) (230538032489 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (230538032489 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1) <
      (-55904062121 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-55904062121 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (53147784423899219535121 / 31250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-55904062121 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP2_arg_eq :
    barrierCase2X0XP2LogArg = barrierComplex (51 / 100) (16801941009 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP2LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP2_arg_regular :
    (barrierCase2X0XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP2LogArg).re := by
  rw [barrierCase2X0XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X0XP2LogArg (1) (1) (322945846669915938081 / 312500000000000000000) (23176941009 / 12500000000) (10426941009 / 12500000000)
  have hratio : ((10426941009 / 12500000000) / (23176941009 / 12500000000) : ℚ) = (3475647003 / 7725647003) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003) <
      (-626091082313 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-626091082313 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (1) (1) (322945846669915938081 / 312500000000000000000) (3475647003 / 7725647003) : ℚ) : ℝ) <
      (-626091082313 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP4_arg_eq :
    barrierCase2X0XP4LogArg = barrierComplex (111 / 400) (40804713879 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP4LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP4_arg_regular :
    (barrierCase2X0XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP4LogArg).re := by
  rw [barrierCase2X0XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X0XP4LogArg (1) (2) (1713153580997055226641 / 1250000000000000000000) (40804713879 / 12500000000) (-111 / 200)
  have hratio : ((-111 / 200) / (40804713879 / 12500000000) : ℚ) = (-2312500000 / 13601571293) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293) <
      (77970853175 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (77970853175 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X0XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (1) (2) (1713153580997055226641 / 1250000000000000000000) (-2312500000 / 13601571293) : ℚ) : ℝ) <
      (77970853175 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP6_arg_eq :
    barrierCase2X0XP6LogArg = barrierComplex (105851377601 / 312500000000) (60496377601 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP6LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP6_arg_regular :
    (barrierCase2X0XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP6LogArg).re := by
  rw [barrierCase2X0XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X0XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X0XP6LogArg (1) (2) (377185684424306936035301 / 195312500000000000000000) (60496377601 / 15625000000) (-105851377601 / 156250000000)
  have hratio : ((-105851377601 / 156250000000) / (60496377601 / 15625000000) : ℚ) = (-105851377601 / 604963776010) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010) <
      (102983412248 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (102983412248 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X0XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (1) (2) (377185684424306936035301 / 195312500000000000000000) (-105851377601 / 604963776010) : ℚ) : ℝ) <
      (102983412248 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X0XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X0 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X0XP8_arg_eq :
    barrierCase2X0XP8LogArg = barrierComplex (-4561377601 / 312500000000) (49916377601 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X0XP8LogArg, Case2PointData.X0, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X0XP8_arg_regular :
    (barrierCase2X0XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X0XP8LogArg).re := by
  rw [barrierCase2X0XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X0XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X0XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X0XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X0XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X0XP8LogArg (1) (2) (249185281446180356035301 / 195312500000000000000000) (49916377601 / 15625000000) (4561377601 / 156250000000)
  have hratio : ((4561377601 / 156250000000) / (49916377601 / 15625000000) : ℚ) = (4561377601 / 499163776010) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X0XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X0XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010) <
      (-153498075605 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X0XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X0 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-153498075605 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X0XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X0XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (1) (2) (249185281446180356035301 / 195312500000000000000000) (4561377601 / 499163776010) : ℚ) : ℝ) <
      (-153498075605 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X0XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
