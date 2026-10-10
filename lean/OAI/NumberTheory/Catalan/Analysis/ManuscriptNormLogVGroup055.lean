import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV12_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV12_9Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV12_9Arg).re

def manuscriptNormV12_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV12_9_arg_eq : manuscriptNormV12_9Arg = barrierComplex (1507 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_9_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_9_exact_interval :
    manuscriptNormV12_9Term ∈ Set.Icc (manuscriptNormV12_9Interval.1 : ℝ) (manuscriptNormV12_9Interval.2 : ℝ) := by
  unfold manuscriptNormV12_9Term
  rw [manuscriptNormV12_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (68110340912023 / 10000000000000000) (-7554608004191 / 2500000000000000)
    manuscriptNormV12_9Arg (-9) (0) (18168392 / 9765625) (1507 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (1507 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_9_rounded_endpoints :
    (-9565262706655637646952898537 / 500000000000000000000000000000) ≤ manuscriptNormV12_9Interval.1 ∧ manuscriptNormV12_9Interval.2 ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_9_enclosure :
    manuscriptNormV12_9Term ∈ Set.Icc ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_9_rounded_endpoints.1
  have hhi : (manuscriptNormV12_9Interval.2 : ℝ) ≤ ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_9_exact_interval.1, manuscriptNormV12_9_exact_interval.2.trans hhi⟩

def manuscriptNormV12_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV12_10Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV12_10Arg).re

def manuscriptNormV12_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV12_10_arg_eq : manuscriptNormV12_10Arg = barrierComplex (48493 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_10_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_10_exact_interval :
    manuscriptNormV12_10Term ∈ Set.Icc (manuscriptNormV12_10Interval.1 : ℝ) (manuscriptNormV12_10Interval.2 : ℝ) := by
  unfold manuscriptNormV12_10Term
  rw [manuscriptNormV12_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000)
    manuscriptNormV12_10Arg (1) (0) (2351571049 / 1250000000) (48493 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (48493 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_10_rounded_endpoints :
    (-1014222019038597977530548497 / 250000000000000000000000000000) ≤ manuscriptNormV12_10Interval.1 ∧ manuscriptNormV12_10Interval.2 ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV12_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_10_enclosure :
    manuscriptNormV12_10Term ∈ Set.Icc ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_10_rounded_endpoints.1
  have hhi : (manuscriptNormV12_10Interval.2 : ℝ) ≤ ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_10_exact_interval.1, manuscriptNormV12_10_exact_interval.2.trans hhi⟩

def manuscriptNormV12_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV12_11Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV12_11Arg).re

def manuscriptNormV12_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV12_11_arg_eq : manuscriptNormV12_11Arg = barrierComplex (496 / 15625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_11_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-47580199826617 / 4000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_11_exact_interval :
    manuscriptNormV12_11Term ∈ Set.Icc (manuscriptNormV12_11Interval.1 : ℝ) (manuscriptNormV12_11Interval.2 : ℝ) := by
  unfold manuscriptNormV12_11Term
  rw [manuscriptNormV12_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-47580199826617 / 4000000000000000) (0 / 1)
    manuscriptNormV12_11Arg (-10) (0) (251920384 / 244140625) (496 / 15625) (0 / 1)
  have hratio : ((0 / 1) / (496 / 15625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_11_rounded_endpoints :
    (20519267757530526706054204969 / 500000000000000000000000000000) ≤ manuscriptNormV12_11Interval.1 ∧ manuscriptNormV12_11Interval.2 ≤ (4103853551506105342014053837 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV12_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_11_enclosure :
    manuscriptNormV12_11Term ∈ Set.Icc ((20519267757530526706054204969 / 500000000000000000000000000000) : ℝ) ((4103853551506105342014053837 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((20519267757530526706054204969 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_11_rounded_endpoints.1
  have hhi : (manuscriptNormV12_11Interval.2 : ℝ) ≤ ((4103853551506105342014053837 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_11_exact_interval.1, manuscriptNormV12_11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
