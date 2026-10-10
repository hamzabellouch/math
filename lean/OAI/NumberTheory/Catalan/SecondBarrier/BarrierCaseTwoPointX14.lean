import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsSixControl
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierCase2X14XV9LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 9 (0, 0)).1

private theorem barrierCase2X14XV9_arg_eq :
    barrierCase2X14XV9LogArg = barrierComplex (1 / 1) (-1388384862363 / 2000000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV9LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV9_arg_regular :
    (barrierCase2X14XV9LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV9LogArg).re := by
  rw [barrierCase2X14XV9_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV9_weight_eq :
    (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV9_error :
    |((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X14XV9LogArg).re -
      ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (5927612526038726453943769 / 4000000000000000000000000) (611615137637 / 3388384862363) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV9_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X14XV9LogArg (0) (-1) (5927612526038726453943769 / 4000000000000000000000000) (3388384862363 / 2000000000000) (611615137637 / 2000000000000)
  have hratio : ((611615137637 / 2000000000000) / (3388384862363 / 2000000000000) : ℚ) = (611615137637 / 3388384862363) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV9_approx_upper :
    barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (5927612526038726453943769 / 4000000000000000000000000) (611615137637 / 3388384862363) <
      (-42724708003 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV9_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 9 (0, 0)) <
      (-42724708003 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X14XV9LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV9_error).2
  have ha : ((barrierWeightedComplexLogRat (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (5927612526038726453943769 / 4000000000000000000000000) (611615137637 / 3388384862363) : ℚ) : ℝ) <
      (-42724708003 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV9_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X14 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X14XP0_arg_eq :
    barrierCase2X14XP0LogArg = barrierComplex (48676478219 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XP0LogArg, Case2PointData.X14, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XP0_arg_regular :
    (barrierCase2X14XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XP0LogArg).re := by
  rw [barrierCase2X14XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X14XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-3) (0) (2369399531804781411961 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X14XP0LogArg (-3) (0) (2369399531804781411961 / 1250000000000000000000) (48676478219 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (48676478219 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-3) (0) (2369399531804781411961 / 1250000000000000000000) (0 / 1) <
      (134468902492 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (134468902492 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X14XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (-3) (0) (2369399531804781411961 / 1250000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (134468902492 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X14 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X14XP1_arg_eq :
    barrierCase2X14XP1LogArg = barrierComplex (129255557429 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XP1LogArg, Case2PointData.X14, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XP1_arg_regular :
    (barrierCase2X14XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XP1LogArg).re := by
  rw [barrierCase2X14XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X14XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-2) (0) (16706999126281517090041 / 15625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X14XP1LogArg (-2) (0) (16706999126281517090041 / 15625000000000000000000) (129255557429 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (129255557429 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-2) (0) (16706999126281517090041 / 15625000000000000000000) (0 / 1) <
      (28253759482 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (28253759482 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X14XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (-2) (0) (16706999126281517090041 / 15625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (28253759482 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV0LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 0 (0, 0)).1

private theorem barrierCase2X14XV0_arg_eq :
    barrierCase2X14XV0LogArg = barrierComplex (19769030693 / 12500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV0LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV0_arg_regular :
    (barrierCase2X14XV0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV0LogArg).re := by
  rw [barrierCase2X14XV0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV0_weight_eq :
    (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV0_error :
    |((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X14XV0LogArg).re -
      ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (390814574540776060249 / 312500000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (15199211 / 100000000) (0 / 1)
    barrierCase2X14XV0LogArg (1) (0) (390814574540776060249 / 312500000000000000000) (19769030693 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (19769030693 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV0_approx_upper :
    barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (390814574540776060249 / 312500000000000000000) (0 / 1) <
      (69671353618 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV0_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 0 (0, 0)) <
      (69671353618 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X14XV0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV0_error).2
  have ha : ((barrierWeightedComplexLogRat (15199211 / 100000000) (0 / 1) (1) (0) (390814574540776060249 / 312500000000000000000) (0 / 1) : ℚ) : ℝ) <
      (69671353618 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV1LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 1 (0, 0)).1

private theorem barrierCase2X14XV1_arg_eq :
    barrierCase2X14XV1LogArg = barrierComplex (53057092079 / 31250000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV1LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV1_arg_regular :
    (barrierCase2X14XV1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV1LogArg).re := by
  rw [barrierCase2X14XV1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV1_weight_eq :
    (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV1_error :
    |((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X14XV1LogArg).re -
      ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (2815055019879484542241 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2225831 / 50000000) (0 / 1)
    barrierCase2X14XV1LogArg (1) (0) (2815055019879484542241 / 1953125000000000000000) (53057092079 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (53057092079 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV1_approx_upper :
    barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (2815055019879484542241 / 1953125000000000000000) (0 / 1) <
      (23564835700 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV1_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 1 (0, 0)) <
      (23564835700 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X14XV1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV1_error).2
  have ha : ((barrierWeightedComplexLogRat (2225831 / 50000000) (0 / 1) (1) (0) (2815055019879484542241 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (23564835700 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV2LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 2 (0, 0)).1

private theorem barrierCase2X14XV2_arg_eq :
    barrierCase2X14XV2LogArg = barrierComplex (45040662377 / 125000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV2LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV2_arg_regular :
    (barrierCase2X14XV2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV2LogArg).re := by
  rw [barrierCase2X14XV2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV2_weight_eq :
    (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV2_error :
    |((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X14XV2LogArg).re -
      ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-3) (0) (2028661267358903290129 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (1272699 / 50000000) (0 / 1)
    barrierCase2X14XV2LogArg (-3) (0) (2028661267358903290129 / 1953125000000000000000) (45040662377 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (45040662377 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV2_approx_upper :
    barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-3) (0) (2028661267358903290129 / 1953125000000000000000) (0 / 1) <
      (-25982100376 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV2_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 2 (0, 0)) <
      (-25982100376 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X14XV2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV2_error).2
  have ha : ((barrierWeightedComplexLogRat (1272699 / 50000000) (0 / 1) (-3) (0) (2028661267358903290129 / 1953125000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-25982100376 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV3LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 3 (0, 0)).1

private theorem barrierCase2X14XV3_arg_eq :
    barrierCase2X14XV3LogArg = barrierComplex (61888416833 / 200000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV3LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV3_arg_regular :
    (barrierCase2X14XV3LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV3LogArg).re := by
  rw [barrierCase2X14XV3_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV3_weight_eq :
    (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV3_error :
    |((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X14XV3LogArg).re -
      ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-4) (0) (3830176138095157749889 / 2500000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV3_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2466317 / 50000000) (0 / 1)
    barrierCase2X14XV3LogArg (-4) (0) (3830176138095157749889 / 2500000000000000000000) (61888416833 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (61888416833 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV3_approx_upper :
    barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-4) (0) (3830176138095157749889 / 2500000000000000000000) (0 / 1) <
      (57859023950 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV3_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 3 (0, 0)) <
      (57859023950 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X14XV3LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV3_error).2
  have ha : ((barrierWeightedComplexLogRat (-2466317 / 50000000) (0 / 1) (-4) (0) (3830176138095157749889 / 2500000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (57859023950 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV3_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV4LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 4 (0, 0)).1

private theorem barrierCase2X14XV4_arg_eq :
    barrierCase2X14XV4LogArg = barrierComplex (355909224761 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV4LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV4_arg_regular :
    (barrierCase2X14XV4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV4LogArg).re := by
  rw [barrierCase2X14XV4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV4_weight_eq :
    (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV4_error :
    |((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X14XV4LogArg).re -
      ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-4) (0) (126671376269976015507121 / 97656250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (11618157 / 100000000) (0 / 1)
    barrierCase2X14XV4LogArg (-4) (0) (126671376269976015507121 / 97656250000000000000000) (355909224761 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (355909224761 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV4_approx_upper :
    barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-4) (0) (126671376269976015507121 / 97656250000000000000000) (0 / 1) <
      (-145949974186 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV4_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 4 (0, 0)) <
      (-145949974186 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X14XV4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV4_error).2
  have ha : ((barrierWeightedComplexLogRat (11618157 / 100000000) (0 / 1) (-4) (0) (126671376269976015507121 / 97656250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-145949974186 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X14XV11LogArg : ℂ :=
  1 - ((Case2PointData.X14 : ℝ) : ℂ) * (barrierV2Tail.getD 11 (0, 0)).1

private theorem barrierCase2X14XV11_arg_eq :
    barrierCase2X14XV11LogArg = barrierComplex (1 / 1) (-894090775239 / 1250000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X14XV11LogArg, Case2PointData.X14, barrierV2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X14XV11_arg_regular :
    (barrierCase2X14XV11LogArg).im ≠ 0 ∨ 0 < (barrierCase2X14XV11LogArg).re := by
  rw [barrierCase2X14XV11_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X14XV11_weight_eq :
    (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;>
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X14XV11_error :
    |((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X14XV11LogArg).re -
      ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2361898314367476015507121 / 1562500000000000000000000) (355909224761 / 2144090775239) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X14XV11_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X14XV11LogArg (0) (-1) (2361898314367476015507121 / 1562500000000000000000000) (2144090775239 / 1250000000000) (355909224761 / 1250000000000)
  have hratio : ((355909224761 / 1250000000000) / (2144090775239 / 1250000000000) : ℚ) = (355909224761 / 2144090775239) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X14XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X14XV11_approx_upper :
    barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2361898314367476015507121 / 1562500000000000000000000) (355909224761 / 2144090775239) <
      (69540068314 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X14XV11_log_upper :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 11 (0, 0)) <
      (69540068314 / 1000000000000 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X14XV11LogArg).re < _
  have he := (abs_lt.mp barrierCase2X14XV11_error).2
  have ha : ((barrierWeightedComplexLogRat (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2361898314367476015507121 / 1562500000000000000000000) (355909224761 / 2144090775239) : ℚ) : ℝ) <
      (69540068314 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14XV11_approx_upper using 1
    norm_num
  linarith

open Case2PointData

private theorem barrierCase2X14_XP_tail_upper :
    (barrierP2Tail.map (barrierCase2XPLogTerm (X14 : ℝ))).sum <
      (475162239770 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [2, 4, 6, 8],
      barrierCase2XPLogTerm (X14 : ℝ) (barrierP2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XPLogTerm (X14 : ℝ) (barrierP2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierP2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X14XP2_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X14XP4_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X14XP6_arg_regular
    · exact barrierCase2XPLogTerm_conj _ _ _ barrierCase2X14XP8_arg_regular
  rw [barrierP2Tail_paired_sum _ hp]
  linarith only [barrierCase2X14XP0_log_upper,
    barrierCase2X14XP1_log_upper,
    barrierCase2X14XP2_log_upper,
    barrierCase2X14XP4_log_upper,
    barrierCase2X14XP6_log_upper,
    barrierCase2X14XP8_log_upper]

private theorem barrierCase2X14_XV_tail_upper :
    (barrierV2Tail.map (barrierCase2XVLogTerm (X14 : ℝ))).sum <
      (388131071528 / 1000000000000 : ℝ) := by
  have hp : ∀ i ∈ [5, 7, 9, 11],
      barrierCase2XVLogTerm (X14 : ℝ) (barrierV2Tail.getD (i + 1) (0, 0)) =
        barrierCase2XVLogTerm (X14 : ℝ) (barrierV2Tail.getD i (0, 0)) := by
    intro i hi
    rw [barrierV2Tail_getD_pair i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X14XV5_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X14XV7_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X14XV9_arg_regular
    · exact barrierCase2XVLogTerm_conj _ _ _ barrierCase2X14XV11_arg_regular
  rw [barrierV2Tail_paired_sum _ hp]
  linarith only [barrierCase2X14XV0_log_upper,
    barrierCase2X14XV1_log_upper,
    barrierCase2X14XV2_log_upper,
    barrierCase2X14XV3_log_upper,
    barrierCase2X14XV4_log_upper,
    barrierCase2X14XV5_log_upper,
    barrierCase2X14XV7_log_upper,
    barrierCase2X14XV9_log_upper,
    barrierCase2X14XV11_log_upper]

private theorem barrierCase2X14_approx_upper :
    barrierCase2XApproxRat X14 (-1) (-2) (0) (7269030693 / 5000000000) (2730969307 / 2500000000) (152838807215776060249 / 100000000000000000000) + (475162239770 / 1000000000000) + (388131071528 / 1000000000000) <
      (-98399 / 100000 - 2 / 1000000000000000 : ℚ) := by
  unfold barrierCase2XApproxRat barrierCase2XRat
  rw [barrierCase2TP_eq_explicit, barrierCase2SV_eq_explicit]
  simp only [barrierScaledLogRat, barrierLogHRat_two_eq]
  decide +kernel

theorem barrierCase2X14_lt : barrierCase2X (X14 : ℝ) < (-98399 / 100000 : ℝ) := by
  have hx : |(X14 : ℝ)| ≤ 1 := by norm_num [X14]
  have he := (abs_lt.mp (barrierCase2X_realLog_approx_error X14 hx
    (-1) (-2) (0) (7269030693 / 5000000000) (2730969307 / 2500000000) (152838807215776060249 / 100000000000000000000)
    X14_normalizations.1 X14_normalizations.2.1 X14_normalizations.2.2)).2
  have ha : ((barrierCase2XApproxRat X14 (-1) (-2) (0) (7269030693 / 5000000000) (2730969307 / 2500000000) (152838807215776060249 / 100000000000000000000) : ℚ) : ℝ) +
      (475162239770 / 1000000000000) + (388131071528 / 1000000000000) < (-98399 / 100000 - 2 / 1000000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X14_approx_upper using 1 <;> norm_num
  linarith only [he, ha, barrierCase2X14_XP_tail_upper, barrierCase2X14_XV_tail_upper]

end InternalCatalan

end

end OAI
