import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV2_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV2_10Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV2_10Arg).re

def manuscriptNormV2_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601)

private theorem manuscriptNormV2_10_arg_eq : manuscriptNormV2_10Arg = barrierComplex (1 / 1) (2101 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_10_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_10_exact_interval :
    manuscriptNormV2_10Term ∈ Set.Icc (manuscriptNormV2_10Interval.1 : ℝ) (manuscriptNormV2_10Interval.2 : ℝ) := by
  unfold manuscriptNormV2_10Term
  rw [manuscriptNormV2_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000)
    manuscriptNormV2_10Arg (0) (1) (10664201 / 6250000) (4601 / 2500) (-399 / 2500)
  have hratio : ((-399 / 2500) / (4601 / 2500) : ℚ) = (-399 / 4601) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_10_rounded_endpoints :
    (128715977164432191110172169 / 100000000000000000000000000000) ≤ manuscriptNormV2_10Interval.1 ∧ manuscriptNormV2_10Interval.2 ≤ (643579885822160983031310613 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV2_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_10_enclosure :
    manuscriptNormV2_10Term ∈ Set.Icc ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_10_rounded_endpoints.1
  have hhi : (manuscriptNormV2_10Interval.2 : ℝ) ≤ ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_10_exact_interval.1, manuscriptNormV2_10_exact_interval.2.trans hhi⟩

def manuscriptNormV2_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV2_11Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV2_11Arg).re

def manuscriptNormV2_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) (0) (-1) (17088061 / 9765625) (419 / 5831)

private theorem manuscriptNormV2_11_arg_eq : manuscriptNormV2_11Arg = barrierComplex (1 / 1) (-2706 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_11_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_11_exact_interval :
    manuscriptNormV2_11Term ∈ Set.Icc (manuscriptNormV2_11Interval.1 : ℝ) (manuscriptNormV2_11Interval.2 : ℝ) := by
  unfold manuscriptNormV2_11Term
  rw [manuscriptNormV2_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2615667529887 / 10000000000000000) (-27637739306451 / 10000000000000000)
    manuscriptNormV2_11Arg (0) (-1) (17088061 / 9765625) (5831 / 3125) (419 / 3125)
  have hratio : ((419 / 3125) / (5831 / 3125) : ℚ) = (419 / 5831) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_11_rounded_endpoints :
    (-2045581158108370136473370921 / 1000000000000000000000000000000) ≤ manuscriptNormV2_11Interval.1 ∧ manuscriptNormV2_11Interval.2 ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV2_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_11_enclosure :
    manuscriptNormV2_11Term ∈ Set.Icc ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_11_rounded_endpoints.1
  have hhi : (manuscriptNormV2_11Interval.2 : ℝ) ≤ ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_11_exact_interval.1, manuscriptNormV2_11_exact_interval.2.trans hhi⟩

def manuscriptNormV2_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV2_12Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV2_12Arg).re

def manuscriptNormV2_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) (0) (1) (17088061 / 9765625) (-419 / 5831)

private theorem manuscriptNormV2_12_arg_eq : manuscriptNormV2_12Arg = barrierComplex (1 / 1) (2706 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_12_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_12_exact_interval :
    manuscriptNormV2_12Term ∈ Set.Icc (manuscriptNormV2_12Interval.1 : ℝ) (manuscriptNormV2_12Interval.2 : ℝ) := by
  unfold manuscriptNormV2_12Term
  rw [manuscriptNormV2_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2615667529887 / 10000000000000000) (27637739306451 / 10000000000000000)
    manuscriptNormV2_12Arg (0) (1) (17088061 / 9765625) (5831 / 3125) (-419 / 3125)
  have hratio : ((-419 / 3125) / (5831 / 3125) : ℚ) = (-419 / 5831) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_12_rounded_endpoints :
    (-2045581158108370136473370921 / 1000000000000000000000000000000) ≤ manuscriptNormV2_12Interval.1 ∧ manuscriptNormV2_12Interval.2 ≤ (-2045581158108370036280529529 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV2_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_12_enclosure :
    manuscriptNormV2_12Term ∈ Set.Icc ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2045581158108370136473370921 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_12_rounded_endpoints.1
  have hhi : (manuscriptNormV2_12Interval.2 : ℝ) ≤ ((-2045581158108370036280529529 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_12_exact_interval.1, manuscriptNormV2_12_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
