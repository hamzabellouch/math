import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV0_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV0_0Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV0_0Arg).re

def manuscriptNormV0_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-231016015022521 / 10000000000000000) (0 / 1) (-3) (0) (648 / 625) (0 / 1)

private theorem manuscriptNormV0_0_arg_eq : manuscriptNormV0_0Arg = barrierComplex (9 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_0_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-231016015022521 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_0_exact_interval :
    manuscriptNormV0_0Term ∈ Set.Icc (manuscriptNormV0_0Interval.1 : ℝ) (manuscriptNormV0_0Interval.2 : ℝ) := by
  unfold manuscriptNormV0_0Term
  rw [manuscriptNormV0_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-231016015022521 / 10000000000000000) (0 / 1)
    manuscriptNormV0_0Arg (-3) (0) (648 / 625) (9 / 25) (0 / 1)
  have hratio : ((0 / 1) / (9 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_0_rounded_endpoints :
    (11800889997381276401084834167 / 500000000000000000000000000000) ≤ manuscriptNormV0_0Interval.1 ∧ manuscriptNormV0_0Interval.2 ≤ (11800889997381276403424736449 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV0_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_0_enclosure :
    manuscriptNormV0_0Term ∈ Set.Icc ((11800889997381276401084834167 / 500000000000000000000000000000) : ℝ) ((11800889997381276403424736449 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((11800889997381276401084834167 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_0_rounded_endpoints.1
  have hhi : (manuscriptNormV0_0Interval.2 : ℝ) ≤ ((11800889997381276403424736449 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_0_exact_interval.1, manuscriptNormV0_0_exact_interval.2.trans hhi⟩

def manuscriptNormV0_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV0_1Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV0_1Arg).re

def manuscriptNormV0_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33830875019341 / 5000000000000000) (0 / 1) (-5) (0) (26912 / 15625) (0 / 1)

private theorem manuscriptNormV0_1_arg_eq : manuscriptNormV0_1Arg = barrierComplex (29 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_1_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-33830875019341 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_1_exact_interval :
    manuscriptNormV0_1Term ∈ Set.Icc (manuscriptNormV0_1Interval.1 : ℝ) (manuscriptNormV0_1Interval.2 : ℝ) := by
  unfold manuscriptNormV0_1Term
  rw [manuscriptNormV0_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33830875019341 / 5000000000000000) (0 / 1)
    manuscriptNormV0_1Arg (-5) (0) (26912 / 15625) (29 / 125) (0 / 1)
  have hratio : ((0 / 1) / (29 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_1_rounded_endpoints :
    (9885502844684175872275224267 / 1000000000000000000000000000000) ≤ manuscriptNormV0_1Interval.1 ∧ manuscriptNormV0_1Interval.2 ≤ (9885502844684175874559747331 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV0_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_1_enclosure :
    manuscriptNormV0_1Term ∈ Set.Icc ((9885502844684175872275224267 / 1000000000000000000000000000000) : ℝ) ((9885502844684175874559747331 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((9885502844684175872275224267 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_1_rounded_endpoints.1
  have hhi : (manuscriptNormV0_1Interval.2 : ℝ) ≤ ((9885502844684175874559747331 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_1_exact_interval.1, manuscriptNormV0_1_exact_interval.2.trans hhi⟩

def manuscriptNormV0_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV0_2Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV0_2Arg).re

def manuscriptNormV0_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1)

private theorem manuscriptNormV0_2_arg_eq : manuscriptNormV0_2Arg = barrierComplex (213 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_2_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-19344020640489 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_2_exact_interval :
    manuscriptNormV0_2Term ∈ Set.Icc (manuscriptNormV0_2Interval.1 : ℝ) (manuscriptNormV0_2Interval.2 : ℝ) := by
  unfold manuscriptNormV0_2Term
  rw [manuscriptNormV0_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-19344020640489 / 5000000000000000) (0 / 1)
    manuscriptNormV0_2Arg (1) (0) (45369 / 31250) (213 / 125) (0 / 1)
  have hratio : ((0 / 1) / (213 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_2_rounded_endpoints :
    (-257748643001069880406345361 / 125000000000000000000000000000) ≤ manuscriptNormV0_2Interval.1 ∧ manuscriptNormV0_2Interval.2 ≤ (-103099457200427952149476101 / 50000000000000000000000000000) := by
  simp only [manuscriptNormV0_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_2_enclosure :
    manuscriptNormV0_2Term ∈ Set.Icc ((-257748643001069880406345361 / 125000000000000000000000000000) : ℝ) ((-103099457200427952149476101 / 50000000000000000000000000000) : ℝ) := by
  have hlo : ((-257748643001069880406345361 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_2_rounded_endpoints.1
  have hhi : (manuscriptNormV0_2Interval.2 : ℝ) ≤ ((-103099457200427952149476101 / 50000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_2_exact_interval.1, manuscriptNormV0_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
