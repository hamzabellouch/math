import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV1_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV1_11Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV1_11Arg).re

def manuscriptNormV1_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) (0) (1) (18479929 / 9765625) (-173 / 6077)

private theorem manuscriptNormV1_11_arg_eq : manuscriptNormV1_11Arg = barrierComplex (1 / 1) (2952 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_11_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_11_exact_interval :
    manuscriptNormV1_11Term ∈ Set.Icc (manuscriptNormV1_11Interval.1 : ℝ) (manuscriptNormV1_11Interval.2 : ℝ) := by
  unfold manuscriptNormV1_11Term
  rw [manuscriptNormV1_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4574556807003 / 10000000000000000) (-48335809895519 / 10000000000000000)
    manuscriptNormV1_11Arg (0) (1) (18479929 / 9765625) (6077 / 3125) (-173 / 3125)
  have hratio : ((-173 / 3125) / (6077 / 3125) : ℚ) = (-173 / 6077) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_11_rounded_endpoints :
    (878208501076450742714674087 / 250000000000000000000000000000) ≤ manuscriptNormV1_11Interval.1 ∧ manuscriptNormV1_11Interval.2 ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_11_enclosure :
    manuscriptNormV1_11Term ∈ Set.Icc ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_11_rounded_endpoints.1
  have hhi : (manuscriptNormV1_11Interval.2 : ℝ) ≤ ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_11_exact_interval.1, manuscriptNormV1_11_exact_interval.2.trans hhi⟩

def manuscriptNormV1_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV1_12Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV1_12Arg).re

def manuscriptNormV1_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) (0) (-1) (18479929 / 9765625) (173 / 6077)

private theorem manuscriptNormV1_12_arg_eq : manuscriptNormV1_12Arg = barrierComplex (1 / 1) (-2952 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_12_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_12_exact_interval :
    manuscriptNormV1_12Term ∈ Set.Icc (manuscriptNormV1_12Interval.1 : ℝ) (manuscriptNormV1_12Interval.2 : ℝ) := by
  unfold manuscriptNormV1_12Term
  rw [manuscriptNormV1_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4574556807003 / 10000000000000000) (48335809895519 / 10000000000000000)
    manuscriptNormV1_12Arg (0) (-1) (18479929 / 9765625) (6077 / 3125) (173 / 3125)
  have hratio : ((173 / 3125) / (6077 / 3125) : ℚ) = (173 / 6077) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_12_rounded_endpoints :
    (878208501076450742714674087 / 250000000000000000000000000000) ≤ manuscriptNormV1_12Interval.1 ∧ manuscriptNormV1_12Interval.2 ≤ (3512834004305803146088280731 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_12_enclosure :
    manuscriptNormV1_12Term ∈ Set.Icc ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((878208501076450742714674087 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_12_rounded_endpoints.1
  have hhi : (manuscriptNormV1_12Interval.2 : ℝ) ≤ ((3512834004305803146088280731 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_12_exact_interval.1, manuscriptNormV1_12_exact_interval.2.trans hhi⟩

def manuscriptNormV2_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV2_0Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV2_0Arg).re

def manuscriptNormV2_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-19344020640489 / 5000000000000000) (0 / 1) (1) (0) (45369 / 31250) (0 / 1)

private theorem manuscriptNormV2_0_arg_eq : manuscriptNormV2_0Arg = barrierComplex (213 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_0_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-19344020640489 / 5000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_0_exact_interval :
    manuscriptNormV2_0Term ∈ Set.Icc (manuscriptNormV2_0Interval.1 : ℝ) (manuscriptNormV2_0Interval.2 : ℝ) := by
  unfold manuscriptNormV2_0Term
  rw [manuscriptNormV2_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-19344020640489 / 5000000000000000) (0 / 1)
    manuscriptNormV2_0Arg (1) (0) (45369 / 31250) (213 / 125) (0 / 1)
  have hratio : ((0 / 1) / (213 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_0_rounded_endpoints :
    (-257748643001069880406345361 / 125000000000000000000000000000) ≤ manuscriptNormV2_0Interval.1 ∧ manuscriptNormV2_0Interval.2 ≤ (-103099457200427952149476101 / 50000000000000000000000000000) := by
  simp only [manuscriptNormV2_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_0_enclosure :
    manuscriptNormV2_0Term ∈ Set.Icc ((-257748643001069880406345361 / 125000000000000000000000000000) : ℝ) ((-103099457200427952149476101 / 50000000000000000000000000000) : ℝ) := by
  have hlo : ((-257748643001069880406345361 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_0_rounded_endpoints.1
  have hhi : (manuscriptNormV2_0Interval.2 : ℝ) ≤ ((-103099457200427952149476101 / 50000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_0_exact_interval.1, manuscriptNormV2_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
