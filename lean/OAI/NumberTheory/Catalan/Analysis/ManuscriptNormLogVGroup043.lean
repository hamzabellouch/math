import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV9_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV9_12Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV9_12Arg).re

def manuscriptNormV9_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV9_12_arg_eq : manuscriptNormV9_12Arg = barrierComplex (1507 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_12_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_12_exact_interval :
    manuscriptNormV9_12Term ∈ Set.Icc (manuscriptNormV9_12Interval.1 : ℝ) (manuscriptNormV9_12Interval.2 : ℝ) := by
  unfold manuscriptNormV9_12Term
  rw [manuscriptNormV9_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000)
    manuscriptNormV9_12Arg (-9) (0) (18168392 / 9765625) (1507 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (1507 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_12_rounded_endpoints :
    (-9565262706655637646952898537 / 500000000000000000000000000000) ≤ manuscriptNormV9_12Interval.1 ∧ manuscriptNormV9_12Interval.2 ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV9_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_12_enclosure :
    manuscriptNormV9_12Term ∈ Set.Icc ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_12_rounded_endpoints.1
  have hhi : (manuscriptNormV9_12Interval.2 : ℝ) ≤ ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_12_exact_interval.1, manuscriptNormV9_12_exact_interval.2.trans hhi⟩

def manuscriptNormV10_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV10_0Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV10_0Arg).re

def manuscriptNormV10_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441)

private theorem manuscriptNormV10_0_arg_eq : manuscriptNormV10_0Arg = barrierComplex (1 / 1) (-191 / 250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_0_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_0_exact_interval :
    manuscriptNormV10_0Term ∈ Set.Icc (manuscriptNormV10_0Interval.1 : ℝ) (manuscriptNormV10_0Interval.2 : ℝ) := by
  unfold manuscriptNormV10_0Term
  rw [manuscriptNormV10_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000)
    manuscriptNormV10_0Arg (0) (-1) (98981 / 62500) (441 / 250) (59 / 250)
  have hratio : ((59 / 250) / (441 / 250) : ℚ) = (59 / 441) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_0_rounded_endpoints :
    (-9251408280602598306119171 / 1953125000000000000000000000) ≤ manuscriptNormV10_0Interval.1 ∧ manuscriptNormV10_0Interval.2 ≤ (-592090129958566250568464173 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV10_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_0_enclosure :
    manuscriptNormV10_0Term ∈ Set.Icc ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ≤ (manuscriptNormV10_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_0_rounded_endpoints.1
  have hhi : (manuscriptNormV10_0Interval.2 : ℝ) ≤ ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_0_exact_interval.1, manuscriptNormV10_0_exact_interval.2.trans hhi⟩

def manuscriptNormV10_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV10_1Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV10_1Arg).re

def manuscriptNormV10_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599)

private theorem manuscriptNormV10_1_arg_eq : manuscriptNormV10_1Arg = barrierComplex (1 / 1) (-573 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_1_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_1_exact_interval :
    manuscriptNormV10_1Term ∈ Set.Icc (manuscriptNormV10_1Interval.1 : ℝ) (manuscriptNormV10_1Interval.2 : ℝ) := by
  unfold manuscriptNormV10_1Term
  rw [manuscriptNormV10_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000)
    manuscriptNormV10_1Arg (0) (-1) (718954 / 390625) (1198 / 625) (52 / 625)
  have hratio : ((52 / 625) / (1198 / 625) : ℚ) = (26 / 599) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_1_rounded_endpoints :
    (-1512993449261219836137063493 / 1000000000000000000000000000000) ≤ manuscriptNormV10_1Interval.1 ∧ manuscriptNormV10_1Interval.2 ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV10_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_1_enclosure :
    manuscriptNormV10_1Term ∈ Set.Icc ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_1_rounded_endpoints.1
  have hhi : (manuscriptNormV10_1Interval.2 : ℝ) ≤ ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_1_exact_interval.1, manuscriptNormV10_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
