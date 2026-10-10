import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X5XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP0_arg_eq :
    barrierCase2X5XP0LogArg = barrierComplex (120257890343 / 50000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP0LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP0_arg_regular :
    (barrierCase2X5XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP0LogArg).re := by
  rw [barrierCase2X5XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X5XP0LogArg (2) (0) (14461960189749012657649 / 10000000000000000000000) (120257890343 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (120257890343 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1) <
      (-163911407703 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-163911407703 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-163911407703 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP1_arg_eq :
    barrierCase2X5XP1LogArg = barrierComplex (329817402713 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP1LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP1_arg_regular :
    (barrierCase2X5XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP1LogArg).re := by
  rw [barrierCase2X5XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X5XP1LogArg (2) (0) (108779519132349219760369 / 62500000000000000000000) (329817402713 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (329817402713 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1) <
      (-41554930187 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-41554930187 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-41554930187 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP2_arg_eq :
    barrierCase2X5XP2LogArg = barrierComplex (51 / 100) (14054719553 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP2LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP2_arg_regular :
    (barrierCase2X5XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP2LogArg).re := by
  rw [barrierCase2X5XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X5XP2LogArg (-1) (1) (360097641713480519809 / 312500000000000000000) (26804719553 / 25000000000) (1304719553 / 25000000000)
  have hratio : ((1304719553 / 25000000000) / (26804719553 / 25000000000) : ℚ) = (76748209 / 1576748209) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209) <
      (-83399800385 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (-83399800385 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209) : ℚ) : ℝ) <
      (-83399800385 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP4_arg_eq :
    barrierCase2X5XP4LogArg = barrierComplex (111 / 400) (34132890343 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP4LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP4_arg_regular :
    (barrierCase2X5XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP4LogArg).re := by
  rw [barrierCase2X5XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X5XP4LogArg (-1) (1) (1357569828167262657649 / 1250000000000000000000) (48007890343 / 50000000000) (20257890343 / 50000000000)
  have hratio : ((20257890343 / 50000000000) / (48007890343 / 50000000000) : ℚ) = (20257890343 / 48007890343) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343) <
      (74873507590 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (74873507590 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-1) (1) (1357569828167262657649 / 1250000000000000000000) (20257890343 / 48007890343) : ℚ) : ℝ) <
      (74873507590 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP6_arg_eq :
    barrierCase2X5XP6LogArg = barrierComplex (147469792817 / 625000000000) (56759792817 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP6LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP6_arg_regular :
    (barrierCase2X5XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP6LogArg).re := by
  rw [barrierCase2X5XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X5XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X5XP6LogArg (-1) (2) (343914747856365384344389 / 195312500000000000000000) (56759792817 / 31250000000) (-147469792817 / 312500000000)
  have hratio : ((-147469792817 / 312500000000) / (56759792817 / 31250000000) : ℚ) = (-147469792817 / 567597928170) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170) <
      (119603537326 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (119603537326 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X5XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-1) (2) (343914747856365384344389 / 195312500000000000000000) (-147469792817 / 567597928170) : ℚ) : ℝ) <
      (119603537326 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X5XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X5 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X5XP8_arg_eq :
    barrierCase2X5XP8LogArg = barrierComplex (55110207183 / 625000000000) (35599792817 / 62500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X5XP8LogArg, Case2PointData.X5, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X5XP8_arg_regular :
    (barrierCase2X5XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X5XP8LogArg).re := by
  rw [barrierCase2X5XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X5XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X5XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X5XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X5XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X5XP8LogArg (-2) (2) (129771659797085664344389 / 97656250000000000000000) (35599792817 / 31250000000) (-55110207183 / 312500000000)
  have hratio : ((-55110207183 / 312500000000) / (35599792817 / 31250000000) : ℚ) = (-55110207183 / 355997928170) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X5XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X5XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170) <
      (-117241478922 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X5XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (-117241478922 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X5XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X5XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (2) (129771659797085664344389 / 97656250000000000000000) (-55110207183 / 355997928170) : ℚ) : ℝ) <
      (-117241478922 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X5XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
