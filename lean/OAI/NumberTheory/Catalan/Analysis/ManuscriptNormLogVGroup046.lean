import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV10_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV10_8Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV10_8Arg).re

def manuscriptNormV10_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV10_8_arg_eq : manuscriptNormV10_8Arg = barrierComplex (3719 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_8_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_8_exact_interval :
    manuscriptNormV10_8Term ∈ Set.Icc (manuscriptNormV10_8Interval.1 : ℝ) (manuscriptNormV10_8Interval.2 : ℝ) := by
  unfold manuscriptNormV10_8Term
  rw [manuscriptNormV10_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-142349837215793 / 10000000000000000) (42818261555831 / 10000000000000000)
    manuscriptNormV10_8Arg (1) (0) (13830961 / 8000000) (3719 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (3719 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_8_rounded_endpoints :
    (-2207517269453298436964373209 / 250000000000000000000000000000) ≤ manuscriptNormV10_8Interval.1 ∧ manuscriptNormV10_8Interval.2 ≤ (-4415034538906596873448011269 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV10_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_8_enclosure :
    manuscriptNormV10_8Term ∈ Set.Icc ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_8_rounded_endpoints.1
  have hhi : (manuscriptNormV10_8Interval.2 : ℝ) ≤ ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_8_exact_interval.1, manuscriptNormV10_8_exact_interval.2.trans hhi⟩

def manuscriptNormV10_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV10_9Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV10_9Arg).re

def manuscriptNormV10_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1)

private theorem manuscriptNormV10_9_arg_eq : manuscriptNormV10_9Arg = barrierComplex (3519 / 40000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_9_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-4667632496657 / 1000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_9_exact_interval :
    manuscriptNormV10_9Term ∈ Set.Icc (manuscriptNormV10_9Interval.1 : ℝ) (manuscriptNormV10_9Interval.2 : ℝ) := by
  unfold manuscriptNormV10_9Term
  rw [manuscriptNormV10_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4667632496657 / 1000000000000000) (0 / 1)
    manuscriptNormV10_9Arg (-8) (0) (12383361 / 6250000) (3519 / 40000) (0 / 1)
  have hratio : ((0 / 1) / (3519 / 40000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_9_rounded_endpoints :
    (5672813212872762508975877099 / 500000000000000000000000000000) ≤ manuscriptNormV10_9Interval.1 ∧ manuscriptNormV10_9Interval.2 ≤ (11345626425745525020670345831 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV10_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_9_enclosure :
    manuscriptNormV10_9Term ∈ Set.Icc ((5672813212872762508975877099 / 500000000000000000000000000000) : ℝ) ((11345626425745525020670345831 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((5672813212872762508975877099 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_9_rounded_endpoints.1
  have hhi : (manuscriptNormV10_9Interval.2 : ℝ) ≤ ((11345626425745525020670345831 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_9_exact_interval.1, manuscriptNormV10_9_exact_interval.2.trans hhi⟩

def manuscriptNormV10_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV10_10Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV10_10Arg).re

def manuscriptNormV10_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1)

private theorem manuscriptNormV10_10_arg_eq : manuscriptNormV10_10Arg = barrierComplex (76481 / 40000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_10_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_10_exact_interval :
    manuscriptNormV10_10Term ∈ Set.Icc (manuscriptNormV10_10Interval.1 : ℝ) (manuscriptNormV10_10Interval.2 : ℝ) := by
  unfold manuscriptNormV10_10Term
  rw [manuscriptNormV10_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3034321589211 / 1250000000000000) (19933793115917 / 5000000000000000)
    manuscriptNormV10_10Arg (1) (0) (5849343361 / 3200000000) (76481 / 40000) (0 / 1)
  have hratio : ((0 / 1) / (76481 / 40000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_10_rounded_endpoints :
    (786693860008045079067253993 / 500000000000000000000000000000) ≤ manuscriptNormV10_10Interval.1 ∧ manuscriptNormV10_10Interval.2 ≤ (1573387720016090158299731593 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV10_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_10_enclosure :
    manuscriptNormV10_10Term ∈ Set.Icc ((786693860008045079067253993 / 500000000000000000000000000000) : ℝ) ((1573387720016090158299731593 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((786693860008045079067253993 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_10_rounded_endpoints.1
  have hhi : (manuscriptNormV10_10Interval.2 : ℝ) ≤ ((1573387720016090158299731593 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_10_exact_interval.1, manuscriptNormV10_10_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
