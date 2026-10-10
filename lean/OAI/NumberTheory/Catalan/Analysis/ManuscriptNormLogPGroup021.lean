import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP6_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP6_4Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP6_4Arg).re

def manuscriptNormP6_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP6_4_arg_eq : manuscriptNormP6_4Arg = barrierComplex (891 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_4_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_4_exact_interval :
    manuscriptNormP6_4Term ∈ Set.Icc (manuscriptNormP6_4Interval.1 : ℝ) (manuscriptNormP6_4Interval.2 : ℝ) := by
  unfold manuscriptNormP6_4Term
  rw [manuscriptNormP6_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000)
    manuscriptNormP6_4Arg (1) (0) (79540981 / 50000000) (891 / 500) (-391 / 5000)
  have hratio : ((-391 / 5000) / (891 / 500) : ℚ) = (-391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_4_rounded_endpoints :
    (136917181857232359070005731 / 200000000000000000000000000000) ≤ manuscriptNormP6_4Interval.1 ∧ manuscriptNormP6_4Interval.2 ≤ (1095337454857858872694069 / 1600000000000000000000000000) := by
  simp only [manuscriptNormP6_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_4_enclosure :
    manuscriptNormP6_4Term ∈ Set.Icc ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
  have hlo : ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_4_rounded_endpoints.1
  have hhi : (manuscriptNormP6_4Interval.2 : ℝ) ≤ ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_4_exact_interval.1, manuscriptNormP6_4_exact_interval.2.trans hhi⟩

def manuscriptNormP6_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP6_5Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP6_5Arg).re

def manuscriptNormP6_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP6_5_arg_eq : manuscriptNormP6_5Arg = barrierComplex (109 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_5_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_5_exact_interval :
    manuscriptNormP6_5Term ∈ Set.Icc (manuscriptNormP6_5Interval.1 : ℝ) (manuscriptNormP6_5Interval.2 : ℝ) := by
  unfold manuscriptNormP6_5Term
  rw [manuscriptNormP6_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-14391556077387 / 10000000000000000) (1045946527347 / 5000000000000000)
    manuscriptNormP6_5Arg (-5) (0) (1340981 / 781250) (109 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (109 / 500) : ℚ) = (391 / 1090) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_5_rounded_endpoints :
    (2033057858870586013559979123 / 1000000000000000000000000000000) ≤ manuscriptNormP6_5Interval.1 ∧ manuscriptNormP6_5Interval.2 ≤ (1016528929435293007022945239 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP6_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_5_enclosure :
    manuscriptNormP6_5Term ∈ Set.Icc ((2033057858870586013559979123 / 1000000000000000000000000000000) : ℝ) ((1016528929435293007022945239 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((2033057858870586013559979123 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_5_rounded_endpoints.1
  have hhi : (manuscriptNormP6_5Interval.2 : ℝ) ≤ ((1016528929435293007022945239 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_5_exact_interval.1, manuscriptNormP6_5_exact_interval.2.trans hhi⟩

def manuscriptNormP6_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP6_6Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP6_6Arg).re

def manuscriptNormP6_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871)

private theorem manuscriptNormP6_6_arg_eq : manuscriptNormP6_6Arg = barrierComplex (114871 / 62500) (-529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_6_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_6_exact_interval :
    manuscriptNormP6_6Term ∈ Set.Icc (manuscriptNormP6_6Interval.1 : ℝ) (manuscriptNormP6_6Interval.2 : ℝ) := by
  unfold manuscriptNormP6_6Term
  rw [manuscriptNormP6_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2165837981751 / 1250000000000000) (-7200437692203 / 5000000000000000)
    manuscriptNormP6_6Arg (1) (0) (13307283041 / 7812500000) (114871 / 62500) (-529 / 3125)
  have hratio : ((-529 / 3125) / (114871 / 62500) : ℚ) = (-10580 / 114871) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_6_rounded_endpoints :
    (464816257410730250422934689 / 500000000000000000000000000000) ≤ manuscriptNormP6_6Interval.1 ∧ manuscriptNormP6_6Interval.2 ≤ (929632514821460500962879519 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP6_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_6_enclosure :
    manuscriptNormP6_6Term ∈ Set.Icc ((464816257410730250422934689 / 500000000000000000000000000000) : ℝ) ((929632514821460500962879519 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((464816257410730250422934689 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_6_rounded_endpoints.1
  have hhi : (manuscriptNormP6_6Interval.2 : ℝ) ≤ ((929632514821460500962879519 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_6_exact_interval.1, manuscriptNormP6_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
