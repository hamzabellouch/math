import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section
namespace InternalCatalan

def barrierCase2X10XP0LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X10 : ℝ) : ℂ) * (barrierP2Tail.getD 0 (0, 0)).1 + (barrierP2Tail.getD 0 (0, 0)).1 ^ 2

private theorem barrierCase2X10XP0_arg_eq :
    barrierCase2X10XP0LogArg = barrierComplex (137018380957 / 100000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XP0LogArg, Case2PointData.X10, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XP0_arg_regular :
    (barrierCase2X10XP0LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XP0LogArg).re := by
  rw [barrierCase2X10XP0_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XP0_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XP0_error :
    |((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X10XP0LogArg).re -
      ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (18774036720077580235849 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XP0_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2334613 / 12500000) (0 / 1)
    barrierCase2X10XP0LogArg (0) (0) (18774036720077580235849 / 10000000000000000000000) (137018380957 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (137018380957 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XP0_approx_upper :
    barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (18774036720077580235849 / 10000000000000000000000) (0 / 1) <
      (-58821956327 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XP0_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 0 (0, 0)) <
      (-58821956327 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X10XP0LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XP0_error).2
  have ha : ((barrierWeightedComplexLogRat (-2334613 / 12500000) (0 / 1) (0) (0) (18774036720077580235849 / 10000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-58821956327 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XP0_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XP1LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X10 : ℝ) : ℂ) * (barrierP2Tail.getD 1 (0, 0)).1 + (barrierP2Tail.getD 1 (0, 0)).1 ^ 2

private theorem barrierCase2X10XP1_arg_eq :
    barrierCase2X10XP1LogArg = barrierComplex (373494935587 / 250000000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XP1LogArg, Case2PointData.X10, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XP1_arg_regular :
    (barrierCase2X10XP1LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XP1LogArg).re := by
  rw [barrierCase2X10XP1_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XP1_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XP1_error :
    |((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X10XP1LogArg).re -
      ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (1) (0) (139498466909137279034569 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XP1_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-2141509 / 50000000) (0 / 1)
    barrierCase2X10XP1LogArg (1) (0) (139498466909137279034569 / 125000000000000000000000) (373494935587 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (373494935587 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XP1_approx_upper :
    barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (1) (0) (139498466909137279034569 / 125000000000000000000000) (0 / 1) <
      (-17193898532 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XP1_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 1 (0, 0)) <
      (-17193898532 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X10XP1LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XP1_error).2
  have ha : ((barrierWeightedComplexLogRat (-2141509 / 50000000) (0 / 1) (1) (0) (139498466909137279034569 / 125000000000000000000000) (0 / 1) : ℚ) : ℝ) <
      (-17193898532 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XP1_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XP2LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X10 : ℝ) : ℂ) * (barrierP2Tail.getD 2 (0, 0)).1 + (barrierP2Tail.getD 2 (0, 0)).1 ^ 2

private theorem barrierCase2X10XP2_arg_eq :
    barrierCase2X10XP2LogArg = barrierComplex (51 / 100) (-14507137253 / 50000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XP2LogArg, Case2PointData.X10, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XP2_arg_regular :
    (barrierCase2X10XP2LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XP2LogArg).re := by
  rw [barrierCase2X10XP2_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XP2_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XP2_error :
    |((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X10XP2LogArg).re -
      ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (860707031277380386009 / 625000000000000000000) (10992862747 / 40007137253) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XP2_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X10XP2LogArg (-2) (-1) (860707031277380386009 / 625000000000000000000) (40007137253 / 50000000000) (10992862747 / 50000000000)
  have hratio : ((10992862747 / 50000000000) / (40007137253 / 50000000000) : ℚ) = (10992862747 / 40007137253) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XP2_approx_upper :
    barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (860707031277380386009 / 625000000000000000000) (10992862747 / 40007137253) <
      (518397838628 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XP2_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 2 (0, 0)) <
      (518397838628 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X10XP2LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XP2_error).2
  have ha : ((barrierWeightedComplexLogRat (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (860707031277380386009 / 625000000000000000000) (10992862747 / 40007137253) : ℚ) : ℝ) <
      (518397838628 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XP2_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XP4LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X10 : ℝ) : ℂ) * (barrierP2Tail.getD 4 (0, 0)).1 + (barrierP2Tail.getD 4 (0, 0)).1 ^ 2

private theorem barrierCase2X10XP4_arg_eq :
    barrierCase2X10XP4LogArg = barrierComplex (111 / 400) (-35231619043 / 100000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XP4LogArg, Case2PointData.X10, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XP4_arg_regular :
    (barrierCase2X10XP4LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XP4LogArg).re := by
  rw [barrierCase2X10XP4_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XP4_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XP4_error :
    |((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X10XP4LogArg).re -
      ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (2011329480391080235849 / 1250000000000000000000) (-7481619043 / 62981619043) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XP4_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X10XP4LogArg (-3) (-1) (2011329480391080235849 / 1250000000000000000000) (62981619043 / 100000000000) (-7481619043 / 100000000000)
  have hratio : ((-7481619043 / 100000000000) / (62981619043 / 100000000000) : ℚ) = (-7481619043 / 62981619043) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XP4_approx_upper :
    barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (2011329480391080235849 / 1250000000000000000000) (-7481619043 / 62981619043) <
      (-44365434840 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XP4_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 4 (0, 0)) <
      (-44365434840 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X10XP4LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XP4_error).2
  have ha : ((barrierWeightedComplexLogRat (-1231651 / 100000000) (-1200529 / 20000000) (-3) (-1) (2011329480391080235849 / 1250000000000000000000) (-7481619043 / 62981619043) : ℚ) : ℝ) <
      (-44365434840 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XP4_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XP6LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X10 : ℝ) : ℂ) * (barrierP2Tail.getD 6 (0, 0)).1 + (barrierP2Tail.getD 6 (0, 0)).1 ^ 2

private theorem barrierCase2X10XP6_arg_eq :
    barrierCase2X10XP6LogArg = barrierComplex (154913691883 / 1250000000000) (-26506308117 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XP6LogArg, Case2PointData.X10, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XP6_arg_regular :
    (barrierCase2X10XP6LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XP6LogArg).re := by
  rw [barrierCase2X10XP6_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XP6_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XP6_error :
    |((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X10XP6LogArg).re -
      ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-5) (-1) (94256688932155068654589 / 48828125000000000000000) (-110149389287 / 419976773053) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XP6_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X10XP6LogArg (-5) (-1) (94256688932155068654589 / 48828125000000000000000) (419976773053 / 1250000000000) (-110149389287 / 1250000000000)
  have hratio : ((-110149389287 / 1250000000000) / (419976773053 / 1250000000000) : ℚ) = (-110149389287 / 419976773053) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XP6_approx_upper :
    barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-5) (-1) (94256688932155068654589 / 48828125000000000000000) (-110149389287 / 419976773053) <
      (-47730687181 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XP6_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 6 (0, 0)) <
      (-47730687181 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X10XP6LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XP6_error).2
  have ha : ((barrierWeightedComplexLogRat (-1612959 / 50000000) (-4464117 / 50000000) (-5) (-1) (94256688932155068654589 / 48828125000000000000000) (-110149389287 / 419976773053) : ℚ) : ℝ) <
      (-47730687181 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XP6_approx_upper using 1
    norm_num
  linarith

def barrierCase2X10XP8LogArg : ℂ :=
  1 - 2 * ((Case2PointData.X10 : ℝ) : ℂ) * (barrierP2Tail.getD 8 (0, 0)).1 + (barrierP2Tail.getD 8 (0, 0)).1 ^ 2

private theorem barrierCase2X10XP8_arg_eq :
    barrierCase2X10XP8LogArg = barrierComplex (250246308117 / 1250000000000) (-68826308117 / 125000000000) := by
  apply Complex.ext <;>
    norm_num [barrierCase2X10XP8LogArg, Case2PointData.X10, barrierP2Tail,
      barrierConjugatePair, barrierComplex, pow_two]

theorem barrierCase2X10XP8_arg_regular :
    (barrierCase2X10XP8LogArg).im ≠ 0 ∨ 0 < (barrierCase2X10XP8LogArg).re := by
  rw [barrierCase2X10XP8_arg_eq]
  norm_num [barrierComplex]

private theorem barrierCase2X10XP8_weight_eq :
    (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;>
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

private theorem barrierCase2X10XP8_error :
    |((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X10XP8LogArg).re -
      ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (-1) (536329283627810508654589 / 390625000000000000000000) (-438016773053 / 938509389287) : ℚ) : ℝ)| <
      (1 / 1000000000000 : ℝ) := by
  rw [barrierCase2X10XP8_weight_eq]
  have herr := barrierWeightedComplexLogRat_error (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X10XP8LogArg (-2) (-1) (536329283627810508654589 / 390625000000000000000000) (938509389287 / 1250000000000) (-438016773053 / 1250000000000)
  have hratio : ((-438016773053 / 1250000000000) / (938509389287 / 1250000000000) : ℚ) = (-438016773053 / 938509389287) := by norm_num
  rw [hratio] at herr
  apply herr
  all_goals
    try rw [barrierCase2X10XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

private theorem barrierCase2X10XP8_approx_upper :
    barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (-1) (536329283627810508654589 / 390625000000000000000000) (-438016773053 / 938509389287) <
      (122358652338 / 1000000000000 - 1 / 1000000000000 : ℚ) := by
  simp only [barrierWeightedComplexLogRat, barrierScaledLogRat, barrierArgApproxRat,
    barrierLogHRat_two_eq, barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem barrierCase2X10XP8_log_upper :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 8 (0, 0)) <
      (122358652338 / 1000000000000 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X10XP8LogArg).re < _
  have he := (abs_lt.mp barrierCase2X10XP8_error).2
  have ha : ((barrierWeightedComplexLogRat (-32899 / 1562500) (9091287 / 100000000) (-2) (-1) (536329283627810508654589 / 390625000000000000000000) (-438016773053 / 938509389287) : ℚ) : ℝ) <
      (122358652338 / 1000000000000 - 1 / 1000000000000 : ℝ) := by
    convert (Rat.cast_lt (K := ℝ)).2 barrierCase2X10XP8_approx_upper using 1
    norm_num
  linarith

end InternalCatalan

end

end OAI
