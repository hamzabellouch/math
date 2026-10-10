import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV7_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV7_5Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV7_5Arg).re

def manuscriptNormV7_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) (1) (0) (724201 / 500000) (0 / 1)

private theorem manuscriptNormV7_5_arg_eq : manuscriptNormV7_5Arg = barrierComplex (851 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_5_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_5_exact_interval :
    manuscriptNormV7_5Term ∈ Set.Icc (manuscriptNormV7_5Interval.1 : ℝ) (manuscriptNormV7_5Interval.2 : ℝ) := by
  unfold manuscriptNormV7_5Term
  rw [manuscriptNormV7_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (251798416946459 / 5000000000000000) (19134814197071 / 2000000000000000)
    manuscriptNormV7_5Arg (1) (0) (724201 / 500000) (851 / 500) (0 / 1)
  have hratio : ((0 / 1) / (851 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_5_rounded_endpoints :
    (2678148258356293550482966351 / 100000000000000000000000000000) ≤ manuscriptNormV7_5Interval.1 ∧ manuscriptNormV7_5Interval.2 ≤ (26781482583562935508230199417 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV7_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_5_enclosure :
    manuscriptNormV7_5Term ∈ Set.Icc ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2678148258356293550482966351 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_5_rounded_endpoints.1
  have hhi : (manuscriptNormV7_5Interval.2 : ℝ) ≤ ((26781482583562935508230199417 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_5_exact_interval.1, manuscriptNormV7_5_exact_interval.2.trans hhi⟩

def manuscriptNormV7_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV7_6Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV7_6Arg).re

def manuscriptNormV7_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7675142212993 / 1000000000000000) (-506825924915957 / 10000000000000000) (-4) (0) (22201 / 15625) (0 / 1)

private theorem manuscriptNormV7_6_arg_eq : manuscriptNormV7_6Arg = barrierComplex (149 / 500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_6_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-7675142212993 / 1000000000000000) (-506825924915957 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_6_exact_interval :
    manuscriptNormV7_6Term ∈ Set.Icc (manuscriptNormV7_6Interval.1 : ℝ) (manuscriptNormV7_6Interval.2 : ℝ) := by
  unfold manuscriptNormV7_6Term
  rw [manuscriptNormV7_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7675142212993 / 1000000000000000) (-506825924915957 / 10000000000000000)
    manuscriptNormV7_6Arg (-4) (0) (22201 / 15625) (149 / 500) (0 / 1)
  have hratio : ((0 / 1) / (149 / 500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_6_rounded_endpoints :
    (9292001429095941576586324869 / 1000000000000000000000000000000) ≤ manuscriptNormV7_6Interval.1 ∧ manuscriptNormV7_6Interval.2 ≤ (1161500178636992697332422467 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV7_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_6_enclosure :
    manuscriptNormV7_6Term ∈ Set.Icc ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((9292001429095941576586324869 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_6_rounded_endpoints.1
  have hhi : (manuscriptNormV7_6Interval.2 : ℝ) ≤ ((1161500178636992697332422467 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_6_exact_interval.1, manuscriptNormV7_6_exact_interval.2.trans hhi⟩

def manuscriptNormV7_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV7_7Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV7_7Arg).re

def manuscriptNormV7_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3545037307063 / 2000000000000000) (118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1)

private theorem manuscriptNormV7_7_arg_eq : manuscriptNormV7_7Arg = barrierComplex (181 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_7_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-3545037307063 / 2000000000000000) (118268659735503 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_7_exact_interval :
    manuscriptNormV7_7Term ∈ Set.Icc (manuscriptNormV7_7Interval.1 : ℝ) (manuscriptNormV7_7Interval.2 : ℝ) := by
  unfold manuscriptNormV7_7Term
  rw [manuscriptNormV7_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3545037307063 / 2000000000000000) (118268659735503 / 2500000000000000)
    manuscriptNormV7_7Arg (1) (0) (32761 / 20000) (181 / 100) (0 / 1)
  have hratio : ((0 / 1) / (181 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_7_rounded_endpoints :
    (-1051682900895782370273743751 / 1000000000000000000000000000000) ≤ manuscriptNormV7_7Interval.1 ∧ manuscriptNormV7_7Interval.2 ≤ (-16432545326496599533657089 / 15625000000000000000000000000) := by
  simp only [manuscriptNormV7_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_7_enclosure :
    manuscriptNormV7_7Term ∈ Set.Icc ((-1051682900895782370273743751 / 1000000000000000000000000000000) : ℝ) ((-16432545326496599533657089 / 15625000000000000000000000000) : ℝ) := by
  have hlo : ((-1051682900895782370273743751 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_7_rounded_endpoints.1
  have hhi : (manuscriptNormV7_7Interval.2 : ℝ) ≤ ((-16432545326496599533657089 / 15625000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_7_exact_interval.1, manuscriptNormV7_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
