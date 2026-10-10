import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP5_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP5_5Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP5_5Arg).re

def manuscriptNormP5_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1)

private theorem manuscriptNormP5_5_arg_eq : manuscriptNormP5_5Arg = barrierComplex (689 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_5_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_5_exact_interval :
    manuscriptNormP5_5Term ∈ Set.Icc (manuscriptNormP5_5Interval.1 : ℝ) (manuscriptNormP5_5Interval.2 : ℝ) := by
  unfold manuscriptNormP5_5Term
  rw [manuscriptNormP5_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2157173925639 / 2500000000000000) (1478632743379 / 4000000000000000)
    manuscriptNormP5_5Arg (1) (0) (474721 / 320000) (689 / 400) (0 / 1)
  have hratio : ((0 / 1) / (689 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_5_rounded_endpoints :
    (469208388071489204587271943 / 1000000000000000000000000000000) ≤ manuscriptNormP5_5Interval.1 ∧ manuscriptNormP5_5Interval.2 ≤ (469208388071489204645537183 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP5_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_5_enclosure :
    manuscriptNormP5_5Term ∈ Set.Icc ((469208388071489204587271943 / 1000000000000000000000000000000) : ℝ) ((469208388071489204645537183 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((469208388071489204587271943 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_5_rounded_endpoints.1
  have hhi : (manuscriptNormP5_5Interval.2 : ℝ) ≤ ((469208388071489204645537183 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_5_exact_interval.1, manuscriptNormP5_5_exact_interval.2.trans hhi⟩

def manuscriptNormP5_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP5_6Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP5_6Arg).re

def manuscriptNormP5_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP5_6_arg_eq : manuscriptNormP5_6Arg = barrierComplex (109 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_6_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_6_exact_interval :
    manuscriptNormP5_6Term ∈ Set.Icc (manuscriptNormP5_6Interval.1 : ℝ) (manuscriptNormP5_6Interval.2 : ℝ) := by
  unfold manuscriptNormP5_6Term
  rw [manuscriptNormP5_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000)
    manuscriptNormP5_6Arg (-5) (0) (1340981 / 781250) (109 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (109 / 500) : ℚ) = (391 / 1090) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_6_rounded_endpoints :
    (2033057858870586013559979123 / 1000000000000000000000000000000) ≤ manuscriptNormP5_6Interval.1 ∧ manuscriptNormP5_6Interval.2 ≤ (1016528929435293007022945239 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP5_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_6_enclosure :
    manuscriptNormP5_6Term ∈ Set.Icc ((2033057858870586013559979123 / 1000000000000000000000000000000) : ℝ) ((1016528929435293007022945239 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((2033057858870586013559979123 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_6_rounded_endpoints.1
  have hhi : (manuscriptNormP5_6Interval.2 : ℝ) ≤ ((1016528929435293007022945239 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_6_exact_interval.1, manuscriptNormP5_6_exact_interval.2.trans hhi⟩

def manuscriptNormP5_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP5_7Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP5_7Arg).re

def manuscriptNormP5_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP5_7_arg_eq : manuscriptNormP5_7Arg = barrierComplex (891 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_7_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_7_exact_interval :
    manuscriptNormP5_7Term ∈ Set.Icc (manuscriptNormP5_7Interval.1 : ℝ) (manuscriptNormP5_7Interval.2 : ℝ) := by
  unfold manuscriptNormP5_7Term
  rw [manuscriptNormP5_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000)
    manuscriptNormP5_7Arg (1) (0) (79540981 / 50000000) (891 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (891 / 500) : ℚ) = (391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_7_rounded_endpoints :
    (136917181857232359070005731 / 200000000000000000000000000000) ≤ manuscriptNormP5_7Interval.1 ∧ manuscriptNormP5_7Interval.2 ≤ (1095337454857858872694069 / 1600000000000000000000000000) := by
  simp only [manuscriptNormP5_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_7_enclosure :
    manuscriptNormP5_7Term ∈ Set.Icc ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
  have hlo : ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_7_rounded_endpoints.1
  have hhi : (manuscriptNormP5_7Interval.2 : ℝ) ≤ ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_7_exact_interval.1, manuscriptNormP5_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
