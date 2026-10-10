import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV5_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV5_7Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV5_7Arg).re

def manuscriptNormV5_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV5_7_arg_eq : manuscriptNormV5_7Arg = barrierComplex (851 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_7_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_7_exact_interval :
    manuscriptNormV5_7Term ∈ Set.Icc (manuscriptNormV5_7Interval.1 : ℝ) (manuscriptNormV5_7Interval.2 : ℝ) := by
  unfold manuscriptNormV5_7Term
  rw [manuscriptNormV5_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000)
    manuscriptNormV5_7Arg (1) (0) (724201 / 500000) (851 / 500) (0 / 1)
  have hratio : ((0 / 1) / (851 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_7_rounded_endpoints :
    (2678148258356293550482966351 / 100000000000000000000000000000) ≤ manuscriptNormV5_7Interval.1 ∧ manuscriptNormV5_7Interval.2 ≤ (26781482583562935508230199417 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV5_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_7_enclosure :
    manuscriptNormV5_7Term ∈ Set.Icc ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_7_rounded_endpoints.1
  have hhi : (manuscriptNormV5_7Interval.2 : ℝ) ≤ ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_7_exact_interval.1, manuscriptNormV5_7_exact_interval.2.trans hhi⟩

def manuscriptNormV5_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV5_8Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV5_8Arg).re

def manuscriptNormV5_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV5_8_arg_eq : manuscriptNormV5_8Arg = barrierComplex (149 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_8_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_8_exact_interval :
    manuscriptNormV5_8Term ∈ Set.Icc (manuscriptNormV5_8Interval.1 : ℝ) (manuscriptNormV5_8Interval.2 : ℝ) := by
  unfold manuscriptNormV5_8Term
  rw [manuscriptNormV5_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000)
    manuscriptNormV5_8Arg (-4) (0) (22201 / 15625) (149 / 500) (0 / 1)
  have hratio : ((0 / 1) / (149 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_8_rounded_endpoints :
    (9292001429095941576586324869 / 1000000000000000000000000000000) ≤ manuscriptNormV5_8Interval.1 ∧ manuscriptNormV5_8Interval.2 ≤ (1161500178636992697332422467 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV5_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_8_enclosure :
    manuscriptNormV5_8Term ∈ Set.Icc ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_8_rounded_endpoints.1
  have hhi : (manuscriptNormV5_8Interval.2 : ℝ) ≤ ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_8_exact_interval.1, manuscriptNormV5_8_exact_interval.2.trans hhi⟩

def manuscriptNormV5_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV5_9Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV5_9Arg).re

def manuscriptNormV5_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV5_9_arg_eq : manuscriptNormV5_9Arg = barrierComplex (17449 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_9_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_9_exact_interval :
    manuscriptNormV5_9Term ∈ Set.Icc (manuscriptNormV5_9Interval.1 : ℝ) (manuscriptNormV5_9Interval.2 : ℝ) := by
  unfold manuscriptNormV5_9Term
  rw [manuscriptNormV5_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000)
    manuscriptNormV5_9Arg (1) (0) (304467601 / 200000000) (17449 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (17449 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_9_rounded_endpoints :
    (-3836731030965981801976136659 / 1000000000000000000000000000000) ≤ manuscriptNormV5_9Interval.1 ∧ manuscriptNormV5_9Interval.2 ≤ (-767346206193196360302151557 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV5_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_9_enclosure :
    manuscriptNormV5_9Term ∈ Set.Icc ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_9_rounded_endpoints.1
  have hhi : (manuscriptNormV5_9Interval.2 : ℝ) ≤ ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_9_exact_interval.1, manuscriptNormV5_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
