import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV8_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV8_4Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV8_4Arg).re

def manuscriptNormV8_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357)

private theorem manuscriptNormV8_4_arg_eq : manuscriptNormV8_4Arg = barrierComplex (1 / 1) (1107 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_4_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_4_exact_interval :
    manuscriptNormV8_4Term ∈ Set.Icc (manuscriptNormV8_4Interval.1 : ℝ) (manuscriptNormV8_4Interval.2 : ℝ) := by
  unfold manuscriptNormV8_4Term
  rw [manuscriptNormV8_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000)
    manuscriptNormV8_4Arg (0) (1) (2787949 / 1562500) (2357 / 1250) (-143 / 1250)
  have hratio : ((-143 / 1250) / (2357 / 1250) : ℚ) = (-143 / 2357) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_4_rounded_endpoints :
    (-7439891480413310489970227707 / 1000000000000000000000000000000) ≤ manuscriptNormV8_4Interval.1 ∧ manuscriptNormV8_4Interval.2 ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV8_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_4_enclosure :
    manuscriptNormV8_4Term ∈ Set.Icc ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_4_rounded_endpoints.1
  have hhi : (manuscriptNormV8_4Interval.2 : ℝ) ≤ ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_4_exact_interval.1, manuscriptNormV8_4_exact_interval.2.trans hhi⟩

def manuscriptNormV8_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV8_5Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV8_5Arg).re

def manuscriptNormV8_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV8_5_arg_eq : manuscriptNormV8_5Arg = barrierComplex (149 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_5_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_5_exact_interval :
    manuscriptNormV8_5Term ∈ Set.Icc (manuscriptNormV8_5Interval.1 : ℝ) (manuscriptNormV8_5Interval.2 : ℝ) := by
  unfold manuscriptNormV8_5Term
  rw [manuscriptNormV8_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7675142212993 / 1000000000000000) (506825924915957 / 10000000000000000)
    manuscriptNormV8_5Arg (-4) (0) (22201 / 15625) (149 / 500) (0 / 1)
  have hratio : ((0 / 1) / (149 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_5_rounded_endpoints :
    (9292001429095941576586324869 / 1000000000000000000000000000000) ≤ manuscriptNormV8_5Interval.1 ∧ manuscriptNormV8_5Interval.2 ≤ (1161500178636992697332422467 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV8_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_5_enclosure :
    manuscriptNormV8_5Term ∈ Set.Icc ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_5_rounded_endpoints.1
  have hhi : (manuscriptNormV8_5Interval.2 : ℝ) ≤ ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_5_exact_interval.1, manuscriptNormV8_5_exact_interval.2.trans hhi⟩

def manuscriptNormV8_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV8_6Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV8_6Arg).re

def manuscriptNormV8_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV8_6_arg_eq : manuscriptNormV8_6Arg = barrierComplex (851 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_6_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_6_exact_interval :
    manuscriptNormV8_6Term ∈ Set.Icc (manuscriptNormV8_6Interval.1 : ℝ) (manuscriptNormV8_6Interval.2 : ℝ) := by
  unfold manuscriptNormV8_6Term
  rw [manuscriptNormV8_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000)
    manuscriptNormV8_6Arg (1) (0) (724201 / 500000) (851 / 500) (0 / 1)
  have hratio : ((0 / 1) / (851 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_6_rounded_endpoints :
    (2678148258356293550482966351 / 100000000000000000000000000000) ≤ manuscriptNormV8_6Interval.1 ∧ manuscriptNormV8_6Interval.2 ≤ (26781482583562935508230199417 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV8_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_6_enclosure :
    manuscriptNormV8_6Term ∈ Set.Icc ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_6_rounded_endpoints.1
  have hhi : (manuscriptNormV8_6Interval.2 : ℝ) ≤ ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_6_exact_interval.1, manuscriptNormV8_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
