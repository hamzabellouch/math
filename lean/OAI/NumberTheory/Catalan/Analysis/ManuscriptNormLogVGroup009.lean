import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV2_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV2_1Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV2_1Arg).re

def manuscriptNormV2_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2832812887869 / 2500000000000000) (0 / 1) (1) (0) (1329409 / 781250) (0 / 1)

private theorem manuscriptNormV2_1_arg_eq : manuscriptNormV2_1Arg = barrierComplex (1153 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_1_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-2832812887869 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_1_exact_interval :
    manuscriptNormV2_1Term ∈ Set.Icc (manuscriptNormV2_1Interval.1 : ℝ) (manuscriptNormV2_1Interval.2 : ℝ) := by
  unfold manuscriptNormV2_1Term
  rw [manuscriptNormV2_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2832812887869 / 2500000000000000) (0 / 1)
    manuscriptNormV2_1Arg (1) (0) (1329409 / 781250) (1153 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1153 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_1_rounded_endpoints :
    (-346946418840094216990697913 / 500000000000000000000000000000) ≤ manuscriptNormV2_1Interval.1 ∧ manuscriptNormV2_1Interval.2 ≤ (-693892837680188433904874467 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV2_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_1_enclosure :
    manuscriptNormV2_1Term ∈ Set.Icc ((-346946418840094216990697913 / 500000000000000000000000000000) : ℝ) ((-693892837680188433904874467 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-346946418840094216990697913 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_1_rounded_endpoints.1
  have hhi : (manuscriptNormV2_1Interval.2 : ℝ) ≤ ((-693892837680188433904874467 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_1_exact_interval.1, manuscriptNormV2_1_exact_interval.2.trans hhi⟩

def manuscriptNormV2_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV2_2Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV2_2Arg).re

def manuscriptNormV2_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1619762744601 / 2500000000000000) (0 / 1) (-5) (0) (636192 / 390625) (0 / 1)

private theorem manuscriptNormV2_2_arg_eq : manuscriptNormV2_2Arg = barrierComplex (141 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_2_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-1619762744601 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_2_exact_interval :
    manuscriptNormV2_2Term ∈ Set.Icc (manuscriptNormV2_2Interval.1 : ℝ) (manuscriptNormV2_2Interval.2 : ℝ) := by
  unfold manuscriptNormV2_2Term
  rw [manuscriptNormV2_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1619762744601 / 2500000000000000) (0 / 1)
    manuscriptNormV2_2Arg (-5) (0) (636192 / 390625) (141 / 625) (0 / 1)
  have hratio : ((0 / 1) / (141 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_2_rounded_endpoints :
    (964725351530545426621073629 / 1000000000000000000000000000000) ≤ manuscriptNormV2_2Interval.1 ∧ manuscriptNormV2_2Interval.2 ≤ (964725351530545426839822669 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV2_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_2_enclosure :
    manuscriptNormV2_2Term ∈ Set.Icc ((964725351530545426621073629 / 1000000000000000000000000000000) : ℝ) ((964725351530545426839822669 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((964725351530545426621073629 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_2_rounded_endpoints.1
  have hhi : (manuscriptNormV2_2Interval.2 : ℝ) ≤ ((964725351530545426839822669 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_2_exact_interval.1, manuscriptNormV2_2_exact_interval.2.trans hhi⟩

def manuscriptNormV2_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 2 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV2_3Term : ℝ :=
  (-((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV2_3Arg).re

def manuscriptNormV2_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3138879179583 / 2500000000000000) (0 / 1) (-6) (0) (26896 / 15625) (0 / 1)

private theorem manuscriptNormV2_3_arg_eq : manuscriptNormV2_3Arg = barrierComplex (41 / 250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV2_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV2_3_weight_eq :
    -((barrierV2Tail.getD 2 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (3138879179583 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV2_3_exact_interval :
    manuscriptNormV2_3Term ∈ Set.Icc (manuscriptNormV2_3Interval.1 : ℝ) (manuscriptNormV2_3Interval.2 : ℝ) := by
  unfold manuscriptNormV2_3Term
  rw [manuscriptNormV2_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3138879179583 / 2500000000000000) (0 / 1)
    manuscriptNormV2_3Arg (-6) (0) (26896 / 15625) (41 / 250) (0 / 1)
  have hratio : ((0 / 1) / (41 / 250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV2_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV2_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV2_3_rounded_endpoints :
    (-2269897869559953121787323801 / 1000000000000000000000000000000) ≤ manuscriptNormV2_3Interval.1 ∧ manuscriptNormV2_3Interval.2 ≤ (-2269897869559953121278620449 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV2_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV2_3_enclosure :
    manuscriptNormV2_3Term ∈ Set.Icc ((-2269897869559953121787323801 / 1000000000000000000000000000000) : ℝ) ((-2269897869559953121278620449 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2269897869559953121787323801 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV2_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_3_rounded_endpoints.1
  have hhi : (manuscriptNormV2_3Interval.2 : ℝ) ≤ ((-2269897869559953121278620449 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV2_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV2_3_exact_interval.1, manuscriptNormV2_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
