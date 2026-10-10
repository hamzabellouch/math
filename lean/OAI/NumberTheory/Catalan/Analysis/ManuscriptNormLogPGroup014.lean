import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP4_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP4_3Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP4_3Arg).re

def manuscriptNormP4_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP4_3_arg_eq : manuscriptNormP4_3Arg = barrierComplex (81 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_3_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_3_exact_interval :
    manuscriptNormP4_3Term ∈ Set.Icc (manuscriptNormP4_3Interval.1 : ℝ) (manuscriptNormP4_3Interval.2 : ℝ) := by
  unfold manuscriptNormP4_3Term
  rw [manuscriptNormP4_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000)
    manuscriptNormP4_3Arg (-3) (0) (6561 / 5000) (81 / 200) (0 / 1)
  have hratio : ((0 / 1) / (81 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_3_rounded_endpoints :
    (-620836233685038813724759441 / 250000000000000000000000000000) ≤ manuscriptNormP4_3Interval.1 ∧ manuscriptNormP4_3Interval.2 ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP4_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_3_enclosure :
    manuscriptNormP4_3Term ∈ Set.Icc ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_3_rounded_endpoints.1
  have hhi : (manuscriptNormP4_3Interval.2 : ℝ) ≤ ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_3_exact_interval.1, manuscriptNormP4_3_exact_interval.2.trans hhi⟩

def manuscriptNormP4_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP4_4Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP4_4Arg).re

def manuscriptNormP4_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) (1) (0) (474721 / 320000) (0 / 1)

private theorem manuscriptNormP4_4_arg_eq : manuscriptNormP4_4Arg = barrierComplex (689 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_4_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_4_exact_interval :
    manuscriptNormP4_4Term ∈ Set.Icc (manuscriptNormP4_4Interval.1 : ℝ) (manuscriptNormP4_4Interval.2 : ℝ) := by
  unfold manuscriptNormP4_4Term
  rw [manuscriptNormP4_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2157173925639 / 2500000000000000) (-1478632743379 / 4000000000000000)
    manuscriptNormP4_4Arg (1) (0) (474721 / 320000) (689 / 400) (0 / 1)
  have hratio : ((0 / 1) / (689 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_4_rounded_endpoints :
    (469208388071489204587271943 / 1000000000000000000000000000000) ≤ manuscriptNormP4_4Interval.1 ∧ manuscriptNormP4_4Interval.2 ≤ (469208388071489204645537183 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP4_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_4_enclosure :
    manuscriptNormP4_4Term ∈ Set.Icc ((469208388071489204587271943 / 1000000000000000000000000000000) : ℝ) ((469208388071489204645537183 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((469208388071489204587271943 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_4_rounded_endpoints.1
  have hhi : (manuscriptNormP4_4Interval.2 : ℝ) ≤ ((469208388071489204645537183 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_4_exact_interval.1, manuscriptNormP4_4_exact_interval.2.trans hhi⟩

def manuscriptNormP4_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP4_5Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP4_5Arg).re

def manuscriptNormP4_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP4_5_arg_eq : manuscriptNormP4_5Arg = barrierComplex (111 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_5_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-18774355590913 / 20000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_5_exact_interval :
    manuscriptNormP4_5Term ∈ Set.Icc (manuscriptNormP4_5Interval.1 : ℝ) (manuscriptNormP4_5Interval.2 : ℝ) := by
  unfold manuscriptNormP4_5Term
  rw [manuscriptNormP4_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-18774355590913 / 20000000000000000) (0 / 1)
    manuscriptNormP4_5Arg (-4) (0) (12321 / 10000) (111 / 400) (0 / 1)
  have hratio : ((0 / 1) / (111 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_5_rounded_endpoints :
    (75210910163037250886802437 / 62500000000000000000000000000) ≤ manuscriptNormP4_5Interval.1 ∧ manuscriptNormP4_5Interval.2 ≤ (1203374562608596014442386537 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP4_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_5_enclosure :
    manuscriptNormP4_5Term ∈ Set.Icc ((75210910163037250886802437 / 62500000000000000000000000000) : ℝ) ((1203374562608596014442386537 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((75210910163037250886802437 / 62500000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_5_rounded_endpoints.1
  have hhi : (manuscriptNormP4_5Interval.2 : ℝ) ≤ ((1203374562608596014442386537 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_5_exact_interval.1, manuscriptNormP4_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
