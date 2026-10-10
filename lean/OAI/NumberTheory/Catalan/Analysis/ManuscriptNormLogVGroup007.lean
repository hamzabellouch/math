import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV1_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV1_8Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV1_8Arg).re

def manuscriptNormV1_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) (0) (-1) (27289 / 15625) (17 / 233)

private theorem manuscriptNormV1_8_arg_eq : manuscriptNormV1_8Arg = barrierComplex (1 / 1) (-108 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_8_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_8_exact_interval :
    manuscriptNormV1_8Term ∈ Set.Icc (manuscriptNormV1_8Interval.1 : ℝ) (manuscriptNormV1_8Interval.2 : ℝ) := by
  unfold manuscriptNormV1_8Term
  rw [manuscriptNormV1_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (17439989085201 / 2500000000000000) (33597567865583 / 5000000000000000)
    manuscriptNormV1_8Arg (0) (-1) (27289 / 15625) (233 / 125) (17 / 125)
  have hratio : ((17 / 125) / (233 / 125) : ℚ) = (17 / 233) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_8_rounded_endpoints :
    (3366521771051272355351880559 / 500000000000000000000000000000) ≤ manuscriptNormV1_8Interval.1 ∧ manuscriptNormV1_8Interval.2 ≤ (1683260885525636238575254391 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV1_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_8_enclosure :
    manuscriptNormV1_8Term ∈ Set.Icc ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_8_rounded_endpoints.1
  have hhi : (manuscriptNormV1_8Interval.2 : ℝ) ≤ ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_8_exact_interval.1, manuscriptNormV1_8_exact_interval.2.trans hhi⟩

def manuscriptNormV1_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV1_9Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV1_9Arg).re

def manuscriptNormV1_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) (0) (1) (718954 / 390625) (-26 / 599)

private theorem manuscriptNormV1_9_arg_eq : manuscriptNormV1_9Arg = barrierComplex (1 / 1) (573 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_9_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_9_exact_interval :
    manuscriptNormV1_9Term ∈ Set.Icc (manuscriptNormV1_9Interval.1 : ℝ) (manuscriptNormV1_9Interval.2 : ℝ) := by
  unfold manuscriptNormV1_9Term
  rw [manuscriptNormV1_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7449346641701 / 5000000000000000) (13257332116537 / 5000000000000000)
    manuscriptNormV1_9Arg (0) (1) (718954 / 390625) (1198 / 625) (-52 / 625)
  have hratio : ((-52 / 625) / (1198 / 625) : ℚ) = (-26 / 599) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_9_rounded_endpoints :
    (-1512993449261219836137063493 / 1000000000000000000000000000000) ≤ manuscriptNormV1_9Interval.1 ∧ manuscriptNormV1_9Interval.2 ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_9_enclosure :
    manuscriptNormV1_9Term ∈ Set.Icc ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_9_rounded_endpoints.1
  have hhi : (manuscriptNormV1_9Interval.2 : ℝ) ≤ ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_9_exact_interval.1, manuscriptNormV1_9_exact_interval.2.trans hhi⟩

def manuscriptNormV1_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV1_10Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV1_10Arg).re

def manuscriptNormV1_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) (0) (-1) (718954 / 390625) (26 / 599)

private theorem manuscriptNormV1_10_arg_eq : manuscriptNormV1_10Arg = barrierComplex (1 / 1) (-573 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_10_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_10_exact_interval :
    manuscriptNormV1_10Term ∈ Set.Icc (manuscriptNormV1_10Interval.1 : ℝ) (manuscriptNormV1_10Interval.2 : ℝ) := by
  unfold manuscriptNormV1_10Term
  rw [manuscriptNormV1_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7449346641701 / 5000000000000000) (-13257332116537 / 5000000000000000)
    manuscriptNormV1_10Arg (0) (-1) (718954 / 390625) (1198 / 625) (52 / 625)
  have hratio : ((52 / 625) / (1198 / 625) : ℚ) = (26 / 599) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_10_rounded_endpoints :
    (-1512993449261219836137063493 / 1000000000000000000000000000000) ≤ manuscriptNormV1_10Interval.1 ∧ manuscriptNormV1_10Interval.2 ≤ (-1512993449261219740014429281 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV1_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_10_enclosure :
    manuscriptNormV1_10Term ∈ Set.Icc ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1512993449261219836137063493 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_10_rounded_endpoints.1
  have hhi : (manuscriptNormV1_10Interval.2 : ℝ) ≤ ((-1512993449261219740014429281 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_10_exact_interval.1, manuscriptNormV1_10_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
