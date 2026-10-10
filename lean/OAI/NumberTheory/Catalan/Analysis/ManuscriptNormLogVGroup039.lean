import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV9_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV9_0Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV9_0Arg).re

def manuscriptNormV9_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441)

private theorem manuscriptNormV9_0_arg_eq : manuscriptNormV9_0Arg = barrierComplex (1 / 1) (191 / 250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_0_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_0_exact_interval :
    manuscriptNormV9_0Term ∈ Set.Icc (manuscriptNormV9_0Interval.1 : ℝ) (manuscriptNormV9_0Interval.2 : ℝ) := by
  unfold manuscriptNormV9_0Term
  rw [manuscriptNormV9_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000)
    manuscriptNormV9_0Arg (0) (1) (98981 / 62500) (441 / 250) (-59 / 250)
  have hratio : ((-59 / 250) / (441 / 250) : ℚ) = (-59 / 441) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_0_rounded_endpoints :
    (-9251408280602598306119171 / 1953125000000000000000000000) ≤ manuscriptNormV9_0Interval.1 ∧ manuscriptNormV9_0Interval.2 ≤ (-592090129958566250568464173 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV9_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_0_enclosure :
    manuscriptNormV9_0Term ∈ Set.Icc ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ≤ (manuscriptNormV9_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_0_rounded_endpoints.1
  have hhi : (manuscriptNormV9_0Interval.2 : ℝ) ≤ ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_0_exact_interval.1, manuscriptNormV9_0_exact_interval.2.trans hhi⟩

def manuscriptNormV9_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV9_1Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV9_1Arg).re

def manuscriptNormV9_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599)

private theorem manuscriptNormV9_1_arg_eq : manuscriptNormV9_1Arg = barrierComplex (1 / 1) (573 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_1_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_1_exact_interval :
    manuscriptNormV9_1Term ∈ Set.Icc (manuscriptNormV9_1Interval.1 : ℝ) (manuscriptNormV9_1Interval.2 : ℝ) := by
  unfold manuscriptNormV9_1Term
  rw [manuscriptNormV9_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000)
    manuscriptNormV9_1Arg (0) (1) (718954 / 390625) (1198 / 625) (-52 / 625)
  have hratio : ((-52 / 625) / (1198 / 625) : ℚ) = (-26 / 599) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_1_rounded_endpoints :
    (-1512993449261219836137063493 / 1000000000000000000000000000000) ≤ manuscriptNormV9_1Interval.1 ∧ manuscriptNormV9_1Interval.2 ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV9_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_1_enclosure :
    manuscriptNormV9_1Term ∈ Set.Icc ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_1_rounded_endpoints.1
  have hhi : (manuscriptNormV9_1Interval.2 : ℝ) ≤ ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_1_exact_interval.1, manuscriptNormV9_1_exact_interval.2.trans hhi⟩

def manuscriptNormV9_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV9_2Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV9_2Arg).re

def manuscriptNormV9_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) (0) (-1) (10664201 / 6250000) (399 / 4601)

private theorem manuscriptNormV9_2_arg_eq : manuscriptNormV9_2Arg = barrierComplex (1 / 1) (-2101 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_2_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_2_exact_interval :
    manuscriptNormV9_2Term ∈ Set.Icc (manuscriptNormV9_2Interval.1 : ℝ) (manuscriptNormV9_2Interval.2 : ℝ) := by
  unfold manuscriptNormV9_2Term
  rw [manuscriptNormV9_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (4259432104929 / 5000000000000000) (7580356876773 / 5000000000000000)
    manuscriptNormV9_2Arg (0) (-1) (10664201 / 6250000) (4601 / 2500) (399 / 2500)
  have hratio : ((399 / 2500) / (4601 / 2500) : ℚ) = (399 / 4601) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_2_rounded_endpoints :
    (128715977164432191110172169 / 100000000000000000000000000000) ≤ manuscriptNormV9_2Interval.1 ∧ manuscriptNormV9_2Interval.2 ≤ (643579885822160983031310613 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV9_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_2_enclosure :
    manuscriptNormV9_2Term ∈ Set.Icc ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_2_rounded_endpoints.1
  have hhi : (manuscriptNormV9_2Interval.2 : ℝ) ≤ ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_2_exact_interval.1, manuscriptNormV9_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
