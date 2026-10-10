import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV1_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV1_5Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV1_5Arg).re

def manuscriptNormV1_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) (0) (1) (609649 / 390625) (-157 / 1093)

private theorem manuscriptNormV1_5_arg_eq : manuscriptNormV1_5Arg = barrierComplex (1 / 1) (468 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_5_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_5_exact_interval :
    manuscriptNormV1_5Term ∈ Set.Icc (manuscriptNormV1_5Interval.1 : ℝ) (manuscriptNormV1_5Interval.2 : ℝ) := by
  unfold manuscriptNormV1_5Term
  rw [manuscriptNormV1_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-30314387010667 / 5000000000000000) (-1337165747419 / 156250000000000)
    manuscriptNormV1_5Arg (0) (1) (609649 / 390625) (1093 / 625) (-157 / 625)
  have hratio : ((-157 / 625) / (1093 / 625) : ℚ) = (-157 / 1093) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_5_rounded_endpoints :
    (518877014766705861242949901 / 125000000000000000000000000000) ≤ manuscriptNormV1_5Interval.1 ∧ manuscriptNormV1_5Interval.2 ≤ (1037754029533411800046178233 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV1_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_5_enclosure :
    manuscriptNormV1_5Term ∈ Set.Icc ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_5_rounded_endpoints.1
  have hhi : (manuscriptNormV1_5Interval.2 : ℝ) ≤ ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_5_exact_interval.1, manuscriptNormV1_5_exact_interval.2.trans hhi⟩

def manuscriptNormV1_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV1_6Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV1_6Arg).re

def manuscriptNormV1_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093)

private theorem manuscriptNormV1_6_arg_eq : manuscriptNormV1_6Arg = barrierComplex (1 / 1) (-468 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_6_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_6_exact_interval :
    manuscriptNormV1_6Term ∈ Set.Icc (manuscriptNormV1_6Interval.1 : ℝ) (manuscriptNormV1_6Interval.2 : ℝ) := by
  unfold manuscriptNormV1_6Term
  rw [manuscriptNormV1_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000)
    manuscriptNormV1_6Arg (0) (-1) (609649 / 390625) (1093 / 625) (157 / 625)
  have hratio : ((157 / 625) / (1093 / 625) : ℚ) = (157 / 1093) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_6_rounded_endpoints :
    (518877014766705861242949901 / 125000000000000000000000000000) ≤ manuscriptNormV1_6Interval.1 ∧ manuscriptNormV1_6Interval.2 ≤ (1037754029533411800046178233 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV1_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_6_enclosure :
    manuscriptNormV1_6Term ∈ Set.Icc ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_6_rounded_endpoints.1
  have hhi : (manuscriptNormV1_6Interval.2 : ℝ) ≤ ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_6_exact_interval.1, manuscriptNormV1_6_exact_interval.2.trans hhi⟩

def manuscriptNormV1_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 1 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV1_7Term : ℝ :=
  (-((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV1_7Arg).re

def manuscriptNormV1_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) (0) (1) (27289 / 15625) (-17 / 233)

private theorem manuscriptNormV1_7_arg_eq : manuscriptNormV1_7Arg = barrierComplex (1 / 1) (108 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV1_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV1_7_weight_eq :
    -((barrierV2Tail.getD 1 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV1_7_exact_interval :
    manuscriptNormV1_7Term ∈ Set.Icc (manuscriptNormV1_7Interval.1 : ℝ) (manuscriptNormV1_7Interval.2 : ℝ) := by
  unfold manuscriptNormV1_7Term
  rw [manuscriptNormV1_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (17439989085201 / 2500000000000000) (-33597567865583 / 5000000000000000)
    manuscriptNormV1_7Arg (0) (1) (27289 / 15625) (233 / 125) (-17 / 125)
  have hratio : ((-17 / 125) / (233 / 125) : ℚ) = (-17 / 233) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV1_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV1_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV1_7_rounded_endpoints :
    (3366521771051272355351880559 / 500000000000000000000000000000) ≤ manuscriptNormV1_7Interval.1 ∧ manuscriptNormV1_7Interval.2 ≤ (1683260885525636238575254391 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV1_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV1_7_enclosure :
    manuscriptNormV1_7Term ∈ Set.Icc ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((3366521771051272355351880559 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV1_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_7_rounded_endpoints.1
  have hhi : (manuscriptNormV1_7Interval.2 : ℝ) ≤ ((1683260885525636238575254391 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV1_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV1_7_exact_interval.1, manuscriptNormV1_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
