import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV10_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV10_2Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV10_2Arg).re

def manuscriptNormV10_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) (0) (1) (10664201 / 6250000) (-399 / 4601)

private theorem manuscriptNormV10_2_arg_eq : manuscriptNormV10_2Arg = barrierComplex (1 / 1) (2101 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_2_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_2_exact_interval :
    manuscriptNormV10_2Term ∈ Set.Icc (manuscriptNormV10_2Interval.1 : ℝ) (manuscriptNormV10_2Interval.2 : ℝ) := by
  unfold manuscriptNormV10_2Term
  rw [manuscriptNormV10_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (4259432104929 / 5000000000000000) (-7580356876773 / 5000000000000000)
    manuscriptNormV10_2Arg (0) (1) (10664201 / 6250000) (4601 / 2500) (-399 / 2500)
  have hratio : ((-399 / 2500) / (4601 / 2500) : ℚ) = (-399 / 4601) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_2_rounded_endpoints :
    (128715977164432191110172169 / 100000000000000000000000000000) ≤ manuscriptNormV10_2Interval.1 ∧ manuscriptNormV10_2Interval.2 ≤ (643579885822160983031310613 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV10_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_2_enclosure :
    manuscriptNormV10_2Term ∈ Set.Icc ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((128715977164432191110172169 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_2_rounded_endpoints.1
  have hhi : (manuscriptNormV10_2Interval.2 : ℝ) ≤ ((643579885822160983031310613 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_2_exact_interval.1, manuscriptNormV10_2_exact_interval.2.trans hhi⟩

def manuscriptNormV10_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV10_3Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV10_3Arg).re

def manuscriptNormV10_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629)

private theorem manuscriptNormV10_3_arg_eq : manuscriptNormV10_3Arg = barrierComplex (1 / 1) (3629 / 4000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_3_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_3_exact_interval :
    manuscriptNormV10_3Term ∈ Set.Icc (manuscriptNormV10_3Interval.1 : ℝ) (manuscriptNormV10_3Interval.2 : ℝ) := by
  unfold manuscriptNormV10_3Term
  rw [manuscriptNormV10_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000)
    manuscriptNormV10_3Arg (0) (1) (29169641 / 16000000) (7629 / 4000) (-371 / 4000)
  have hratio : ((-371 / 4000) / (7629 / 4000) : ℚ) = (-371 / 7629) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_3_rounded_endpoints :
    (-1330194736875770427300979589 / 500000000000000000000000000000) ≤ manuscriptNormV10_3Interval.1 ∧ manuscriptNormV10_3Interval.2 ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV10_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_3_enclosure :
    manuscriptNormV10_3Term ∈ Set.Icc ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_3_rounded_endpoints.1
  have hhi : (manuscriptNormV10_3Interval.2 : ℝ) ≤ ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_3_exact_interval.1, manuscriptNormV10_3_exact_interval.2.trans hhi⟩

def manuscriptNormV10_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV10_4Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV10_4Arg).re

def manuscriptNormV10_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) (0) (1) (1176921049 / 625000000) (-1507 / 48493)

private theorem manuscriptNormV10_4_arg_eq : manuscriptNormV10_4Arg = barrierComplex (1 / 1) (23493 / 25000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_4_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_4_exact_interval :
    manuscriptNormV10_4Term ∈ Set.Icc (manuscriptNormV10_4Interval.1 : ℝ) (manuscriptNormV10_4Interval.2 : ℝ) := by
  unfold manuscriptNormV10_4Term
  rw [manuscriptNormV10_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (38883310921047 / 10000000000000000) (-69199218597939 / 10000000000000000)
    manuscriptNormV10_4Arg (0) (1) (1176921049 / 625000000) (48493 / 25000) (-1507 / 25000)
  have hratio : ((-1507 / 25000) / (48493 / 25000) : ℚ) = (-1507 / 48493) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_4_rounded_endpoints :
    (6450387944343331493548784039 / 1000000000000000000000000000000) ≤ manuscriptNormV10_4Interval.1 ∧ manuscriptNormV10_4Interval.2 ≤ (3225193972171665872211150519 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV10_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_4_enclosure :
    manuscriptNormV10_4Term ∈ Set.Icc ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((6450387944343331493548784039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_4_rounded_endpoints.1
  have hhi : (manuscriptNormV10_4Interval.2 : ℝ) ≤ ((3225193972171665872211150519 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_4_exact_interval.1, manuscriptNormV10_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
