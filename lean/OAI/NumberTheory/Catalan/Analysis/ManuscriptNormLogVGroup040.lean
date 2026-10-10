import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV9_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV9_3Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV9_3Arg).re

def manuscriptNormV9_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629)

private theorem manuscriptNormV9_3_arg_eq : manuscriptNormV9_3Arg = barrierComplex (1 / 1) (-3629 / 4000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_3_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_3_exact_interval :
    manuscriptNormV9_3Term ∈ Set.Icc (manuscriptNormV9_3Interval.1 : ℝ) (manuscriptNormV9_3Interval.2 : ℝ) := by
  unfold manuscriptNormV9_3Term
  rw [manuscriptNormV9_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000)
    manuscriptNormV9_3Arg (0) (-1) (29169641 / 16000000) (7629 / 4000) (371 / 4000)
  have hratio : ((371 / 4000) / (7629 / 4000) : ℚ) = (371 / 7629) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_3_rounded_endpoints :
    (-1330194736875770427300979589 / 500000000000000000000000000000) ≤ manuscriptNormV9_3Interval.1 ∧ manuscriptNormV9_3Interval.2 ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV9_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_3_enclosure :
    manuscriptNormV9_3Term ∈ Set.Icc ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_3_rounded_endpoints.1
  have hhi : (manuscriptNormV9_3Interval.2 : ℝ) ≤ ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_3_exact_interval.1, manuscriptNormV9_3_exact_interval.2.trans hhi⟩

def manuscriptNormV9_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV9_4Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV9_4Arg).re

def manuscriptNormV9_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) (0) (-1) (1176921049 / 625000000) (1507 / 48493)

private theorem manuscriptNormV9_4_arg_eq : manuscriptNormV9_4Arg = barrierComplex (1 / 1) (-23493 / 25000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_4_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_4_exact_interval :
    manuscriptNormV9_4Term ∈ Set.Icc (manuscriptNormV9_4Interval.1 : ℝ) (manuscriptNormV9_4Interval.2 : ℝ) := by
  unfold manuscriptNormV9_4Term
  rw [manuscriptNormV9_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (38883310921047 / 10000000000000000) (69199218597939 / 10000000000000000)
    manuscriptNormV9_4Arg (0) (-1) (1176921049 / 625000000) (48493 / 25000) (1507 / 25000)
  have hratio : ((1507 / 25000) / (48493 / 25000) : ℚ) = (1507 / 48493) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_4_rounded_endpoints :
    (6450387944343331493548784039 / 1000000000000000000000000000000) ≤ manuscriptNormV9_4Interval.1 ∧ manuscriptNormV9_4Interval.2 ≤ (3225193972171665872211150519 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV9_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_4_enclosure :
    manuscriptNormV9_4Term ∈ Set.Icc ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_4_rounded_endpoints.1
  have hhi : (manuscriptNormV9_4Interval.2 : ℝ) ≤ ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_4_exact_interval.1, manuscriptNormV9_4_exact_interval.2.trans hhi⟩

def manuscriptNormV9_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV9_5Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV9_5Arg).re

def manuscriptNormV9_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV9_5_arg_eq : manuscriptNormV9_5Arg = barrierComplex (17449 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_5_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_5_exact_interval :
    manuscriptNormV9_5Term ∈ Set.Icc (manuscriptNormV9_5Interval.1 : ℝ) (manuscriptNormV9_5Interval.2 : ℝ) := by
  unfold manuscriptNormV9_5Term
  rw [manuscriptNormV9_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-68919525805689 / 10000000000000000) (145456838557667 / 10000000000000000)
    manuscriptNormV9_5Arg (1) (0) (304467601 / 200000000) (17449 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (17449 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_5_rounded_endpoints :
    (-3836731030965981801976136659 / 1000000000000000000000000000000) ≤ manuscriptNormV9_5Interval.1 ∧ manuscriptNormV9_5Interval.2 ≤ (-767346206193196360302151557 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV9_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_5_enclosure :
    manuscriptNormV9_5Term ∈ Set.Icc ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_5_rounded_endpoints.1
  have hhi : (manuscriptNormV9_5Interval.2 : ℝ) ≤ ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_5_exact_interval.1, manuscriptNormV9_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
