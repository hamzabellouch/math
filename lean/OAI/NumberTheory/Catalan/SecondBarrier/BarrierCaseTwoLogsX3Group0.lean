import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X3XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP0_arg_eq :
    barrierCase2X3XP0LogArg = barrierComplex (141403855749 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP0LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP0_arg_regular :
    (barrierCase2X3XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP0LogArg).re := by
  rw [barrierCase2X3XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X3XP0LogArg (2) (0) (19995050420684000351001 / 10000000000000000000000) (141403855749 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (141403855749 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1) <
      (-194164536672 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-194164536672 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-194164536672 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP1_arg_eq :
    barrierCase2X3XP1LogArg = barrierComplex (388279777659 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP1LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP1_arg_regular :
    (barrierCase2X3XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP1LogArg).re := by
  rw [barrierCase2X3XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X3XP1LogArg (3) (0) (150761185738922475520281 / 125000000000000000000000) (388279777659 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (388279777659 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1) <
      (-48544257915 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-48544257915 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-48544257915 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP2_arg_eq :
    barrierCase2X3XP2LogArg = barrierComplex (51 / 100) (22761881779 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP2LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP2_arg_regular :
    (barrierCase2X3XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP2LogArg).re := by
  rw [barrierCase2X3XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X3XP2LogArg (0) (1) (680665762121172204841 / 625000000000000000000) (35511881779 / 25000000000) (10011881779 / 25000000000)
  have hratio : ((10011881779 / 25000000000) / (35511881779 / 25000000000) : ℚ) = (10011881779 / 35511881779) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779) <
      (-366556874260 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-366556874260 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779) : ℚ) : ℝ) <
      (-366556874260 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP4_arg_eq :
    barrierCase2X3XP4LogArg = barrierComplex (111 / 400) (55278855749 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP4LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP4_arg_regular :
    (barrierCase2X3XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP4LogArg).re := by
  rw [barrierCase2X3XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X3XP4LogArg (0) (2) (3248267517918750351001 / 2500000000000000000000) (55278855749 / 25000000000) (-111 / 200)
  have hratio : ((-111 / 200) / (55278855749 / 25000000000) : ℚ) = (-13875000000 / 55278855749) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749) <
      (77915215782 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (77915215782 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (0) (2) (3248267517918750351001 / 2500000000000000000000) (-13875000000 / 55278855749) : ℚ) : ℝ) <
      (77915215782 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP6_arg_eq :
    barrierCase2X3XP6LogArg = barrierComplex (176079040131 / 625000000000) (85369040131 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP6LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP6_arg_regular :
    (barrierCase2X3XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP6LogArg).re := by
  rw [barrierCase2X3XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X3XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X3XP6LogArg (0) (2) (759791129662283158213261 / 390625000000000000000000) (85369040131 / 31250000000) (-176079040131 / 312500000000)
  have hratio : ((-176079040131 / 312500000000) / (85369040131 / 31250000000) : ℚ) = (-176079040131 / 853690401310) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310) <
      (111353046691 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (111353046691 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X3XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (0) (2) (759791129662283158213261 / 390625000000000000000000) (-176079040131 / 853690401310) : ℚ) : ℝ) <
      (111353046691 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X3XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X3 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X3XP8_arg_eq :
    barrierCase2X3XP8LogArg = barrierComplex (26500959869 / 625000000000) (64209040131 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X3XP8LogArg, Case2PointData.X3, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X3XP8_arg_regular :
    (barrierCase2X3XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X3XP8LogArg).re := by
  rw [barrierCase2X3XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X3XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X3XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X3XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X3XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X3XP8LogArg (0) (2) (412982384328415198213261 / 390625000000000000000000) (64209040131 / 31250000000) (-26500959869 / 312500000000)
  have hratio : ((-26500959869 / 312500000000) / (64209040131 / 31250000000) : ℚ) = (-26500959869 / 642090401310) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X3XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X3XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310) <
      (-139641427292 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X3XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-139641427292 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X3XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X3XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (0) (2) (412982384328415198213261 / 390625000000000000000000) (-26500959869 / 642090401310) : ℚ) : ℝ) <
      (-139641427292 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X3XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
