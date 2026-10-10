import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP1_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP1_6Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP1_6Arg).re

def manuscriptNormP1_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) (0) (-1) (247249661 / 156250000) (609 / 22229)

private theorem manuscriptNormP1_6_arg_eq : manuscriptNormP1_6Arg = barrierComplex (11419 / 12500) (-1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_6_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_6_exact_interval :
    manuscriptNormP1_6Term ∈ Set.Icc (manuscriptNormP1_6Interval.1 : ℝ) (manuscriptNormP1_6Interval.2 : ℝ) := by
  unfold manuscriptNormP1_6Term
  rw [manuscriptNormP1_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3454166215131 / 10000000000000000) (-9559946732553 / 10000000000000000)
    manuscriptNormP1_6Arg (0) (-1) (247249661 / 156250000) (22229 / 12500) (609 / 12500)
  have hratio : ((609 / 12500) / (22229 / 12500) : ℚ) = (609 / 22229) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_6_rounded_endpoints :
    (-200978735801924450580405149 / 250000000000000000000000000000) ≤ manuscriptNormP1_6Interval.1 ∧ manuscriptNormP1_6Interval.2 ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_6_enclosure :
    manuscriptNormP1_6Term ∈ Set.Icc ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_6_rounded_endpoints.1
  have hhi : (manuscriptNormP1_6Interval.2 : ℝ) ≤ ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_6_exact_interval.1, manuscriptNormP1_6_exact_interval.2.trans hhi⟩

def manuscriptNormP1_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP1_7Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP1_7Arg).re

def manuscriptNormP1_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) (0) (1) (247249661 / 156250000) (-609 / 22229)

private theorem manuscriptNormP1_7_arg_eq : manuscriptNormP1_7Arg = barrierComplex (11419 / 12500) (1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_7_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_7_exact_interval :
    manuscriptNormP1_7Term ∈ Set.Icc (manuscriptNormP1_7Interval.1 : ℝ) (manuscriptNormP1_7Interval.2 : ℝ) := by
  unfold manuscriptNormP1_7Term
  rw [manuscriptNormP1_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3454166215131 / 10000000000000000) (9559946732553 / 10000000000000000)
    manuscriptNormP1_7Arg (0) (1) (247249661 / 156250000) (22229 / 12500) (-609 / 12500)
  have hratio : ((-609 / 12500) / (22229 / 12500) : ℚ) = (-609 / 22229) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_7_rounded_endpoints :
    (-200978735801924450580405149 / 250000000000000000000000000000) ≤ manuscriptNormP1_7Interval.1 ∧ manuscriptNormP1_7Interval.2 ≤ (-803914943207697767664729149 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_7_enclosure :
    manuscriptNormP1_7Term ∈ Set.Icc ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-200978735801924450580405149 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_7_rounded_endpoints.1
  have hhi : (manuscriptNormP1_7Interval.2 : ℝ) ≤ ((-803914943207697767664729149 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_7_exact_interval.1, manuscriptNormP1_7_exact_interval.2.trans hhi⟩

def manuscriptNormP1_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP1_8Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP1_8Arg).re

def manuscriptNormP1_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391)

private theorem manuscriptNormP1_8_arg_eq : manuscriptNormP1_8Arg = barrierComplex (13581 / 12500) (-1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_8_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_8_exact_interval :
    manuscriptNormP1_8Term ∈ Set.Icc (manuscriptNormP1_8Interval.1 : ℝ) (manuscriptNormP1_8Interval.2 : ℝ) := by
  unfold manuscriptNormP1_8Term
  rw [manuscriptNormP1_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000)
    manuscriptNormP1_8Arg (0) (-1) (301299661 / 156250000) (24391 / 12500) (2771 / 12500)
  have hratio : ((2771 / 12500) / (24391 / 12500) : ℚ) = (2771 / 24391) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_8_rounded_endpoints :
    (29020409128306298718006873 / 50000000000000000000000000000) ≤ manuscriptNormP1_8Interval.1 ∧ manuscriptNormP1_8Interval.2 ≤ (580408182566126009652303041 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_8_enclosure :
    manuscriptNormP1_8Term ∈ Set.Icc ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_8_rounded_endpoints.1
  have hhi : (manuscriptNormP1_8Interval.2 : ℝ) ≤ ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_8_exact_interval.1, manuscriptNormP1_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
