import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV9_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV9_9Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV9_9Arg).re

def manuscriptNormV9_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3034321589211 / 1250000000000000) (-19933793115917 / 5000000000000000) (1) (0) (5849343361 / 3200000000) (0 / 1)

private theorem manuscriptNormV9_9_arg_eq : manuscriptNormV9_9Arg = barrierComplex (76481 / 40000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_9_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (3034321589211 / 1250000000000000) (-19933793115917 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_9_exact_interval :
    manuscriptNormV9_9Term ∈ Set.Icc (manuscriptNormV9_9Interval.1 : ℝ) (manuscriptNormV9_9Interval.2 : ℝ) := by
  unfold manuscriptNormV9_9Term
  rw [manuscriptNormV9_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3034321589211 / 1250000000000000) (-19933793115917 / 5000000000000000)
    manuscriptNormV9_9Arg (1) (0) (5849343361 / 3200000000) (76481 / 40000) (0 / 1)
  have hratio : ((0 / 1) / (76481 / 40000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_9_rounded_endpoints :
    (786693860008045079067253993 / 500000000000000000000000000000) ≤ manuscriptNormV9_9Interval.1 ∧ manuscriptNormV9_9Interval.2 ≤ (1573387720016090158299731593 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV9_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_9_enclosure :
    manuscriptNormV9_9Term ∈ Set.Icc ((786693860008045079067253993 / 500000000000000000000000000000) : ℝ) ((1573387720016090158299731593 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((786693860008045079067253993 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_9_rounded_endpoints.1
  have hhi : (manuscriptNormV9_9Interval.2 : ℝ) ≤ ((1573387720016090158299731593 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_9_exact_interval.1, manuscriptNormV9_9_exact_interval.2.trans hhi⟩

def manuscriptNormV9_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV9_10Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV9_10Arg).re

def manuscriptNormV9_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4667632496657 / 1000000000000000) (0 / 1) (-8) (0) (12383361 / 6250000) (0 / 1)

private theorem manuscriptNormV9_10_arg_eq : manuscriptNormV9_10Arg = barrierComplex (3519 / 40000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_10_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (-4667632496657 / 1000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_10_exact_interval :
    manuscriptNormV9_10Term ∈ Set.Icc (manuscriptNormV9_10Interval.1 : ℝ) (manuscriptNormV9_10Interval.2 : ℝ) := by
  unfold manuscriptNormV9_10Term
  rw [manuscriptNormV9_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4667632496657 / 1000000000000000) (0 / 1)
    manuscriptNormV9_10Arg (-8) (0) (12383361 / 6250000) (3519 / 40000) (0 / 1)
  have hratio : ((0 / 1) / (3519 / 40000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_10_rounded_endpoints :
    (5672813212872762508975877099 / 500000000000000000000000000000) ≤ manuscriptNormV9_10Interval.1 ∧ manuscriptNormV9_10Interval.2 ≤ (11345626425745525020670345831 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV9_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_10_enclosure :
    manuscriptNormV9_10Term ∈ Set.Icc ((5672813212872762508975877099 / 500000000000000000000000000000) : ℝ) ((11345626425745525020670345831 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((5672813212872762508975877099 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_10_rounded_endpoints.1
  have hhi : (manuscriptNormV9_10Interval.2 : ℝ) ≤ ((11345626425745525020670345831 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_10_exact_interval.1, manuscriptNormV9_10_exact_interval.2.trans hhi⟩

def manuscriptNormV9_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV9_11Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV9_11Arg).re

def manuscriptNormV9_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV9_11_arg_eq : manuscriptNormV9_11Arg = barrierComplex (48493 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_11_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-2391875533 / 390625000000) (8491908331363 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_11_exact_interval :
    manuscriptNormV9_11Term ∈ Set.Icc (manuscriptNormV9_11Interval.1 : ℝ) (manuscriptNormV9_11Interval.2 : ℝ) := by
  unfold manuscriptNormV9_11Term
  rw [manuscriptNormV9_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2391875533 / 390625000000) (8491908331363 / 2000000000000000)
    manuscriptNormV9_11Arg (1) (0) (2351571049 / 1250000000) (48493 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (48493 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_11_rounded_endpoints :
    (-1014222019038597977530548497 / 250000000000000000000000000000) ≤ manuscriptNormV9_11Interval.1 ∧ manuscriptNormV9_11Interval.2 ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV9_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_11_enclosure :
    manuscriptNormV9_11Term ∈ Set.Icc ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_11_rounded_endpoints.1
  have hhi : (manuscriptNormV9_11Interval.2 : ℝ) ≤ ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_11_exact_interval.1, manuscriptNormV9_11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
