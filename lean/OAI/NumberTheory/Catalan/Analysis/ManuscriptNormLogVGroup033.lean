import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV7_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV7_8Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV7_8Arg).re

def manuscriptNormV7_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1)

private theorem manuscriptNormV7_8_arg_eq : manuscriptNormV7_8Arg = barrierComplex (19 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_8_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-473406586612213 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_8_exact_interval :
    manuscriptNormV7_8Term ∈ Set.Icc (manuscriptNormV7_8Interval.1 : ℝ) (manuscriptNormV7_8Interval.2 : ℝ) := by
  unfold manuscriptNormV7_8Term
  rw [manuscriptNormV7_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-473406586612213 / 10000000000000000) (0 / 1)
    manuscriptNormV7_8Arg (-5) (0) (722 / 625) (19 / 100) (0 / 1)
  have hratio : ((0 / 1) / (19 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_8_rounded_endpoints :
    (7862010919018189014159228319 / 100000000000000000000000000000) ≤ manuscriptNormV7_8Interval.1 ∧ manuscriptNormV7_8Interval.2 ≤ (4913756824386368134848479063 / 62500000000000000000000000000) := by
  simp only [manuscriptNormV7_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_8_enclosure :
    manuscriptNormV7_8Term ∈ Set.Icc ((7862010919018189014159228319 / 100000000000000000000000000000) : ℝ) ((4913756824386368134848479063 / 62500000000000000000000000000) : ℝ) := by
  have hlo : ((7862010919018189014159228319 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_8_rounded_endpoints.1
  have hhi : (manuscriptNormV7_8Interval.2 : ℝ) ≤ ((4913756824386368134848479063 / 62500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_8_exact_interval.1, manuscriptNormV7_8_exact_interval.2.trans hhi⟩

def manuscriptNormV7_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV7_9Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV7_9Arg).re

def manuscriptNormV7_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-142349837215793 / 10000000000000000) (-42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV7_9_arg_eq : manuscriptNormV7_9Arg = barrierComplex (3719 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_9_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-142349837215793 / 10000000000000000) (-42818261555831 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_9_exact_interval :
    manuscriptNormV7_9Term ∈ Set.Icc (manuscriptNormV7_9Interval.1 : ℝ) (manuscriptNormV7_9Interval.2 : ℝ) := by
  unfold manuscriptNormV7_9Term
  rw [manuscriptNormV7_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-142349837215793 / 10000000000000000) (-42818261555831 / 10000000000000000)
    manuscriptNormV7_9Arg (1) (0) (13830961 / 8000000) (3719 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (3719 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_9_rounded_endpoints :
    (-2207517269453298436964373209 / 250000000000000000000000000000) ≤ manuscriptNormV7_9Interval.1 ∧ manuscriptNormV7_9Interval.2 ≤ (-4415034538906596873448011269 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV7_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_9_enclosure :
    manuscriptNormV7_9Term ∈ Set.Icc ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_9_rounded_endpoints.1
  have hhi : (manuscriptNormV7_9Interval.2 : ℝ) ≤ ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_9_exact_interval.1, manuscriptNormV7_9_exact_interval.2.trans hhi⟩

def manuscriptNormV7_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV7_10Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV7_10Arg).re

def manuscriptNormV7_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV7_10_arg_eq : manuscriptNormV7_10Arg = barrierComplex (281 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_10_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_10_exact_interval :
    manuscriptNormV7_10Term ∈ Set.Icc (manuscriptNormV7_10Interval.1 : ℝ) (manuscriptNormV7_10Interval.2 : ℝ) := by
  unfold manuscriptNormV7_10Term
  rw [manuscriptNormV7_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000)
    manuscriptNormV7_10Arg (-6) (0) (78961 / 62500) (281 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (281 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_10_rounded_endpoints :
    (-1837847806637300544349037963 / 250000000000000000000000000000) ≤ manuscriptNormV7_10Interval.1 ∧ manuscriptNormV7_10Interval.2 ≤ (-735139122654920217587852529 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV7_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_10_enclosure :
    manuscriptNormV7_10Term ∈ Set.Icc ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_10_rounded_endpoints.1
  have hhi : (manuscriptNormV7_10Interval.2 : ℝ) ≤ ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_10_exact_interval.1, manuscriptNormV7_10_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
