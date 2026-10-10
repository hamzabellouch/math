import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV11_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV11_10Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV11_10Arg).re

def manuscriptNormV11_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV11_10_arg_eq : manuscriptNormV11_10Arg = barrierComplex (1507 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_10_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_10_exact_interval :
    manuscriptNormV11_10Term ∈ Set.Icc (manuscriptNormV11_10Interval.1 : ℝ) (manuscriptNormV11_10Interval.2 : ℝ) := by
  unfold manuscriptNormV11_10Term
  rw [manuscriptNormV11_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000)
    manuscriptNormV11_10Arg (-9) (0) (18168392 / 9765625) (1507 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (1507 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_10_rounded_endpoints :
    (-9565262706655637646952898537 / 500000000000000000000000000000) ≤ manuscriptNormV11_10Interval.1 ∧ manuscriptNormV11_10Interval.2 ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_10_enclosure :
    manuscriptNormV11_10Term ∈ Set.Icc ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_10_rounded_endpoints.1
  have hhi : (manuscriptNormV11_10Interval.2 : ℝ) ≤ ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_10_exact_interval.1, manuscriptNormV11_10_exact_interval.2.trans hhi⟩

def manuscriptNormV11_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV11_11Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV11_11Arg).re

def manuscriptNormV11_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) (1) (0) (472904258 / 244140625) (0 / 1)

private theorem manuscriptNormV11_11_arg_eq : manuscriptNormV11_11Arg = barrierComplex (30754 / 15625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_11_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_11_exact_interval :
    manuscriptNormV11_11Term ∈ Set.Icc (manuscriptNormV11_11Interval.1 : ℝ) (manuscriptNormV11_11Interval.2 : ℝ) := by
  unfold manuscriptNormV11_11Term
  rw [manuscriptNormV11_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (58419274664429 / 5000000000000000) (-44630695170837 / 20000000000000000)
    manuscriptNormV11_11Arg (1) (0) (472904258 / 244140625) (30754 / 15625) (0 / 1)
  have hratio : ((0 / 1) / (30754 / 15625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_11_rounded_endpoints :
    (988962187297497831790278377 / 125000000000000000000000000000) ≤ manuscriptNormV11_11Interval.1 ∧ manuscriptNormV11_11Interval.2 ≤ (7911697498379982655265387197 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_11_enclosure :
    manuscriptNormV11_11Term ∈ Set.Icc ((988962187297497831790278377 / 125000000000000000000000000000) : ℝ) ((7911697498379982655265387197 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((988962187297497831790278377 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_11_rounded_endpoints.1
  have hhi : (manuscriptNormV11_11Interval.2 : ℝ) ≤ ((7911697498379982655265387197 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_11_exact_interval.1, manuscriptNormV11_11_exact_interval.2.trans hhi⟩

def manuscriptNormV11_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV11_12Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV11_12Arg).re

def manuscriptNormV11_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-47580199826617 / 4000000000000000) (0 / 1) (-10) (0) (251920384 / 244140625) (0 / 1)

private theorem manuscriptNormV11_12_arg_eq : manuscriptNormV11_12Arg = barrierComplex (496 / 15625) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_12_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-47580199826617 / 4000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_12_exact_interval :
    manuscriptNormV11_12Term ∈ Set.Icc (manuscriptNormV11_12Interval.1 : ℝ) (manuscriptNormV11_12Interval.2 : ℝ) := by
  unfold manuscriptNormV11_12Term
  rw [manuscriptNormV11_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-47580199826617 / 4000000000000000) (0 / 1)
    manuscriptNormV11_12Arg (-10) (0) (251920384 / 244140625) (496 / 15625) (0 / 1)
  have hratio : ((0 / 1) / (496 / 15625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_12_rounded_endpoints :
    (20519267757530526706054204969 / 500000000000000000000000000000) ≤ manuscriptNormV11_12Interval.1 ∧ manuscriptNormV11_12Interval.2 ≤ (4103853551506105342014053837 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV11_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_12_enclosure :
    manuscriptNormV11_12Term ∈ Set.Icc ((20519267757530526706054204969 / 500000000000000000000000000000) : ℝ) ((4103853551506105342014053837 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((20519267757530526706054204969 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_12_rounded_endpoints.1
  have hhi : (manuscriptNormV11_12Interval.2 : ℝ) ≤ ((4103853551506105342014053837 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_12_exact_interval.1, manuscriptNormV11_12_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
