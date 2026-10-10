import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV6_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV6_9Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV6_9Arg).re

def manuscriptNormV6_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (160081263898183 / 10000000000000000) (16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV6_9_arg_eq : manuscriptNormV6_9Arg = barrierComplex (2551 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_9_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (160081263898183 / 10000000000000000) (16780401343011 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_9_exact_interval :
    manuscriptNormV6_9Term ∈ Set.Icc (manuscriptNormV6_9Interval.1 : ℝ) (manuscriptNormV6_9Interval.2 : ℝ) := by
  unfold manuscriptNormV6_9Term
  rw [manuscriptNormV6_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (160081263898183 / 10000000000000000) (16780401343011 / 10000000000000000)
    manuscriptNormV6_9Arg (-4) (0) (6507601 / 6250000) (2551 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (2551 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_9_rounded_endpoints :
    (-2733586989958455530919248339 / 125000000000000000000000000000) ≤ manuscriptNormV6_9Interval.1 ∧ manuscriptNormV6_9Interval.2 ≤ (-10934347959833822121515096977 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV6_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_9_enclosure :
    manuscriptNormV6_9Term ∈ Set.Icc ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_9_rounded_endpoints.1
  have hhi : (manuscriptNormV6_9Interval.2 : ℝ) ≤ ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_9_exact_interval.1, manuscriptNormV6_9_exact_interval.2.trans hhi⟩

def manuscriptNormV6_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV6_10Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV6_10Arg).re

def manuscriptNormV6_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV6_10_arg_eq : manuscriptNormV6_10Arg = barrierComplex (17449 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_10_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_10_exact_interval :
    manuscriptNormV6_10Term ∈ Set.Icc (manuscriptNormV6_10Interval.1 : ℝ) (manuscriptNormV6_10Interval.2 : ℝ) := by
  unfold manuscriptNormV6_10Term
  rw [manuscriptNormV6_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000)
    manuscriptNormV6_10Arg (1) (0) (304467601 / 200000000) (17449 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (17449 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_10_rounded_endpoints :
    (-3836731030965981801976136659 / 1000000000000000000000000000000) ≤ manuscriptNormV6_10Interval.1 ∧ manuscriptNormV6_10Interval.2 ≤ (-767346206193196360302151557 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV6_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_10_enclosure :
    manuscriptNormV6_10Term ∈ Set.Icc ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_10_rounded_endpoints.1
  have hhi : (manuscriptNormV6_10Interval.2 : ℝ) ≤ ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_10_exact_interval.1, manuscriptNormV6_10_exact_interval.2.trans hhi⟩

def manuscriptNormV6_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV6_11Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV6_11Arg).re

def manuscriptNormV6_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV6_11_arg_eq : manuscriptNormV6_11Arg = barrierComplex (1453 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_11_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_11_exact_interval :
    manuscriptNormV6_11Term ∈ Set.Icc (manuscriptNormV6_11Interval.1 : ℝ) (manuscriptNormV6_11Interval.2 : ℝ) := by
  unfold manuscriptNormV6_11Term
  rw [manuscriptNormV6_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000)
    manuscriptNormV6_11Arg (-5) (0) (16889672 / 9765625) (1453 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (1453 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_11_rounded_endpoints :
    (4061860828661937773552758353 / 125000000000000000000000000000) ≤ manuscriptNormV6_11Interval.1 ∧ manuscriptNormV6_11Interval.2 ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV6_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_11_enclosure :
    manuscriptNormV6_11Term ∈ Set.Icc ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_11_rounded_endpoints.1
  have hhi : (manuscriptNormV6_11Interval.2 : ℝ) ≤ ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_11_exact_interval.1, manuscriptNormV6_11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
