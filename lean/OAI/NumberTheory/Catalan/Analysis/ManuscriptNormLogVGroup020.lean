import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV4_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV4_8Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV4_8Arg).re

def manuscriptNormV4_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) (0) (1) (2787949 / 1562500) (-143 / 2357)

private theorem manuscriptNormV4_8_arg_eq : manuscriptNormV4_8Arg = barrierComplex (1 / 1) (1107 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_8_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_8_exact_interval :
    manuscriptNormV4_8Term ∈ Set.Icc (manuscriptNormV4_8Interval.1 : ℝ) (manuscriptNormV4_8Interval.2 : ℝ) := by
  unfold manuscriptNormV4_8Term
  rw [manuscriptNormV4_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (91031408615547 / 5000000000000000) (175369027693701 / 10000000000000000)
    manuscriptNormV4_8Arg (0) (1) (2787949 / 1562500) (2357 / 1250) (-143 / 1250)
  have hratio : ((-143 / 1250) / (2357 / 1250) : ℚ) = (-143 / 2357) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_8_rounded_endpoints :
    (-7439891480413310489970227707 / 1000000000000000000000000000000) ≤ manuscriptNormV4_8Interval.1 ∧ manuscriptNormV4_8Interval.2 ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_8_enclosure :
    manuscriptNormV4_8Term ∈ Set.Icc ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_8_rounded_endpoints.1
  have hhi : (manuscriptNormV4_8Interval.2 : ℝ) ≤ ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_8_exact_interval.1, manuscriptNormV4_8_exact_interval.2.trans hhi⟩

def manuscriptNormV4_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV4_9Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV4_9Arg).re

def manuscriptNormV4_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493)

private theorem manuscriptNormV4_9_arg_eq : manuscriptNormV4_9Arg = barrierComplex (1 / 1) (-23493 / 25000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_9_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_9_exact_interval :
    manuscriptNormV4_9Term ∈ Set.Icc (manuscriptNormV4_9Interval.1 : ℝ) (manuscriptNormV4_9Interval.2 : ℝ) := by
  unfold manuscriptNormV4_9Term
  rw [manuscriptNormV4_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000)
    manuscriptNormV4_9Arg (0) (-1) (1176921049 / 625000000) (48493 / 25000) (1507 / 25000)
  have hratio : ((1507 / 25000) / (48493 / 25000) : ℚ) = (1507 / 48493) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_9_rounded_endpoints :
    (6450387944343331493548784039 / 1000000000000000000000000000000) ≤ manuscriptNormV4_9Interval.1 ∧ manuscriptNormV4_9Interval.2 ≤ (3225193972171665872211150519 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV4_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_9_enclosure :
    manuscriptNormV4_9Term ∈ Set.Icc ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_9_rounded_endpoints.1
  have hhi : (manuscriptNormV4_9Interval.2 : ℝ) ≤ ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_9_exact_interval.1, manuscriptNormV4_9_exact_interval.2.trans hhi⟩

def manuscriptNormV4_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV4_10Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV4_10Arg).re

def manuscriptNormV4_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493)

private theorem manuscriptNormV4_10_arg_eq : manuscriptNormV4_10Arg = barrierComplex (1 / 1) (23493 / 25000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_10_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_10_exact_interval :
    manuscriptNormV4_10Term ∈ Set.Icc (manuscriptNormV4_10Interval.1 : ℝ) (manuscriptNormV4_10Interval.2 : ℝ) := by
  unfold manuscriptNormV4_10Term
  rw [manuscriptNormV4_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000)
    manuscriptNormV4_10Arg (0) (1) (1176921049 / 625000000) (48493 / 25000) (-1507 / 25000)
  have hratio : ((-1507 / 25000) / (48493 / 25000) : ℚ) = (-1507 / 48493) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_10_rounded_endpoints :
    (6450387944343331493548784039 / 1000000000000000000000000000000) ≤ manuscriptNormV4_10Interval.1 ∧ manuscriptNormV4_10Interval.2 ≤ (3225193972171665872211150519 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV4_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_10_enclosure :
    manuscriptNormV4_10Term ∈ Set.Icc ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_10_rounded_endpoints.1
  have hhi : (manuscriptNormV4_10Interval.2 : ℝ) ≤ ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_10_exact_interval.1, manuscriptNormV4_10_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
