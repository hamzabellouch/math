import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV6_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV6_6Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV6_6Arg).re

def manuscriptNormV6_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7362962422863 / 400000000000000) (8181815098393 / 156250000000000) (1) (0) (16168441 / 12500000) (0 / 1)

private theorem manuscriptNormV6_6_arg_eq : manuscriptNormV6_6Arg = barrierComplex (4021 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_6_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (7362962422863 / 400000000000000) (8181815098393 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_6_exact_interval :
    manuscriptNormV6_6Term ∈ Set.Icc (manuscriptNormV6_6Interval.1 : ℝ) (manuscriptNormV6_6Interval.2 : ℝ) := by
  unfold manuscriptNormV6_6Term
  rw [manuscriptNormV6_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7362962422863 / 400000000000000) (8181815098393 / 156250000000000)
    manuscriptNormV6_6Arg (1) (0) (16168441 / 12500000) (4021 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (4021 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_6_rounded_endpoints :
    (1093491717623458862478015627 / 125000000000000000000000000000) ≤ manuscriptNormV6_6Interval.1 ∧ manuscriptNormV6_6Interval.2 ≤ (2186983435246917725266771121 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV6_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_6_enclosure :
    manuscriptNormV6_6Term ∈ Set.Icc ((1093491717623458862478015627 / 125000000000000000000000000000) : ℝ) ((2186983435246917725266771121 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((1093491717623458862478015627 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_6_rounded_endpoints.1
  have hhi : (manuscriptNormV6_6Interval.2 : ℝ) ≤ ((2186983435246917725266771121 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_6_exact_interval.1, manuscriptNormV6_6_exact_interval.2.trans hhi⟩

def manuscriptNormV6_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV6_7Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV6_7Arg).re

def manuscriptNormV6_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7675142212993 / 1000000000000000) (-506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV6_7_arg_eq : manuscriptNormV6_7Arg = barrierComplex (149 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_7_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-7675142212993 / 1000000000000000) (-506825924915957 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_7_exact_interval :
    manuscriptNormV6_7Term ∈ Set.Icc (manuscriptNormV6_7Interval.1 : ℝ) (manuscriptNormV6_7Interval.2 : ℝ) := by
  unfold manuscriptNormV6_7Term
  rw [manuscriptNormV6_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7675142212993 / 1000000000000000) (-506825924915957 / 10000000000000000)
    manuscriptNormV6_7Arg (-4) (0) (22201 / 15625) (149 / 500) (0 / 1)
  have hratio : ((0 / 1) / (149 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_7_rounded_endpoints :
    (9292001429095941576586324869 / 1000000000000000000000000000000) ≤ manuscriptNormV6_7Interval.1 ∧ manuscriptNormV6_7Interval.2 ≤ (1161500178636992697332422467 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV6_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_7_enclosure :
    manuscriptNormV6_7Term ∈ Set.Icc ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_7_rounded_endpoints.1
  have hhi : (manuscriptNormV6_7Interval.2 : ℝ) ≤ ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_7_exact_interval.1, manuscriptNormV6_7_exact_interval.2.trans hhi⟩

def manuscriptNormV6_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV6_8Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV6_8Arg).re

def manuscriptNormV6_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV6_8_arg_eq : manuscriptNormV6_8Arg = barrierComplex (851 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_8_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_8_exact_interval :
    manuscriptNormV6_8Term ∈ Set.Icc (manuscriptNormV6_8Interval.1 : ℝ) (manuscriptNormV6_8Interval.2 : ℝ) := by
  unfold manuscriptNormV6_8Term
  rw [manuscriptNormV6_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (251798416946459 / 5000000000000000) (-19134814197071 / 2000000000000000)
    manuscriptNormV6_8Arg (1) (0) (724201 / 500000) (851 / 500) (0 / 1)
  have hratio : ((0 / 1) / (851 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_8_rounded_endpoints :
    (2678148258356293550482966351 / 100000000000000000000000000000) ≤ manuscriptNormV6_8Interval.1 ∧ manuscriptNormV6_8Interval.2 ≤ (26781482583562935508230199417 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV6_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_8_enclosure :
    manuscriptNormV6_8Term ∈ Set.Icc ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_8_rounded_endpoints.1
  have hhi : (manuscriptNormV6_8Interval.2 : ℝ) ≤ ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_8_exact_interval.1, manuscriptNormV6_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
