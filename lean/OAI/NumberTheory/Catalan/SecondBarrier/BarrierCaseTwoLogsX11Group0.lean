import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X11XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X11 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X11XP0_arg_eq :
    barrierCase2X11XP0LogArg = barrierComplex (29427707443 / 25000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XP0LogArg, Case2PointData.X11, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XP0_arg_regular :
    (barrierCase2X11XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XP0LogArg).re := by
  rw [barrierCase2X11XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X11XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X11XP0LogArg (0) (0) (865989965350797598249 / 625000000000000000000) (29427707443 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (29427707443 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1) <
      (-30454715744 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-30454715744 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X11XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-30454715744 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X11 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X11XP1_arg_eq :
    barrierCase2X11XP1LogArg = barrierComplex (80028808813 / 62500000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XP1LogArg, Case2PointData.X11, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XP1_arg_regular :
    (barrierCase2X11XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XP1LogArg).re := by
  rw [barrierCase2X11XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X11XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X11XP1LogArg (0) (0) (6404610240027706468969 / 3906250000000000000000) (80028808813 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (80028808813 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1) <
      (-10588482378 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-10588482378 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X11XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-10588482378 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X11 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X11XP2_arg_eq :
    barrierCase2X11XP2LogArg = barrierComplex (51 / 100) (-5614326347 / 12500000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XP2LogArg, Case2PointData.X11, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XP2_arg_regular :
    (barrierCase2X11XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XP2LogArg).re := by
  rw [barrierCase2X11XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X11XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X11XP2LogArg (-2) (-1) (72161285330618364409 / 39062500000000000000) (11989326347 / 12500000000) (760673653 / 12500000000)
  have hratio : ((760673653 / 12500000000) / (11989326347 / 12500000000) : ℚ) = (44745509 / 705254491) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491) <
      (486400749591 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (486400749591 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X11XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491) : ℚ) : ℝ) <
      (486400749591 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X11 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X11XP4_arg_eq :
    barrierCase2X11XP4LogArg = barrierComplex (111 / 400) (-13634792557 / 25000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XP4LogArg, Case2PointData.X11, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XP4_arg_regular :
    (barrierCase2X11XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XP4LogArg).re := by
  rw [barrierCase2X11XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X11XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X11XP4LogArg (-2) (-1) (234036474322422598249 / 156250000000000000000) (20572292557 / 25000000000) (-6697292557 / 25000000000)
  have hratio : ((-6697292557 / 25000000000) / (20572292557 / 25000000000) : ℚ) = (-6697292557 / 20572292557) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557) <
      (-59987601142 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-59987601142 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X11XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-2) (-1) (234036474322422598249 / 156250000000000000000) (-6697292557 / 20572292557) : ℚ) : ℝ) <
      (-59987601142 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X11 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X11XP6_arg_eq :
    barrierCase2X11XP6LogArg = barrierComplex (32197927717 / 312500000000) (-13157072283 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XP6LogArg, Case2PointData.X11, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XP6_arg_regular :
    (barrierCase2X11XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XP6LogArg).re := by
  rw [barrierCase2X11XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X11XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X11XP6LogArg (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (13157072283 / 15625000000) (32197927717 / 156250000000)
  have hratio : ((32197927717 / 156250000000) / (13157072283 / 15625000000) : ℚ) = (32197927717 / 131570722830) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830) <
      (-91848390024 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-91848390024 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X11XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-3) (-2) (18347561655277840040989 / 12207031250000000000000) (32197927717 / 131570722830) : ℚ) : ℝ) <
      (-91848390024 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X11XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X11 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X11XP8_arg_eq :
    barrierCase2X11XP8LogArg = barrierComplex (69092072283 / 312500000000) (-23737072283 / 31250000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X11XP8LogArg, Case2PointData.X11, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X11XP8_arg_regular :
    (barrierCase2X11XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X11XP8LogArg).re := by
  rw [barrierCase2X11XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X11XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X11XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X11XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X11XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X11XP8LogArg (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (23737072283 / 15625000000) (69092072283 / 156250000000)
  have hratio : ((69092072283 / 156250000000) / (23737072283 / 15625000000) : ℚ) = (69092072283 / 237370722830) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X11XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X11XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830) <
      (121988531026 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X11XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (121988531026 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X11XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X11XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-1) (-2) (61118574509195980040989 / 48828125000000000000000) (69092072283 / 237370722830) : ℚ) : ℝ) <
      (121988531026 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X11XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
