import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP5_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP5_2Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP5_2Arg).re

def manuscriptNormP5_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP5_2_arg_eq : manuscriptNormP5_2Arg = barrierComplex (81 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_2_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_2_exact_interval :
    manuscriptNormP5_2Term ∈ Set.Icc (manuscriptNormP5_2Interval.1 : ℝ) (manuscriptNormP5_2Interval.2 : ℝ) := by
  unfold manuscriptNormP5_2Term
  rw [manuscriptNormP5_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000)
    manuscriptNormP5_2Arg (-3) (0) (6561 / 5000) (81 / 200) (0 / 1)
  have hratio : ((0 / 1) / (81 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_2_rounded_endpoints :
    (-620836233685038813724759441 / 250000000000000000000000000000) ≤ manuscriptNormP5_2Interval.1 ∧ manuscriptNormP5_2Interval.2 ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP5_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_2_enclosure :
    manuscriptNormP5_2Term ∈ Set.Icc ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_2_rounded_endpoints.1
  have hhi : (manuscriptNormP5_2Interval.2 : ℝ) ≤ ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_2_exact_interval.1, manuscriptNormP5_2_exact_interval.2.trans hhi⟩

def manuscriptNormP5_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP5_3Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP5_3Arg).re

def manuscriptNormP5_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP5_3_arg_eq : manuscriptNormP5_3Arg = barrierComplex (319 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_3_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_3_exact_interval :
    manuscriptNormP5_3Term ∈ Set.Icc (manuscriptNormP5_3Interval.1 : ℝ) (manuscriptNormP5_3Interval.2 : ℝ) := by
  unfold manuscriptNormP5_3Term
  rw [manuscriptNormP5_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000)
    manuscriptNormP5_3Arg (1) (0) (101761 / 80000) (319 / 200) (0 / 1)
  have hratio : ((0 / 1) / (319 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_3_rounded_endpoints :
    (-127531733280728920730965549 / 40000000000000000000000000000) ≤ manuscriptNormP5_3Interval.1 ∧ manuscriptNormP5_3Interval.2 ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP5_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_3_enclosure :
    manuscriptNormP5_3Term ∈ Set.Icc ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_3_rounded_endpoints.1
  have hhi : (manuscriptNormP5_3Interval.2 : ℝ) ≤ ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_3_exact_interval.1, manuscriptNormP5_3_exact_interval.2.trans hhi⟩

def manuscriptNormP5_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP5_4Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP5_4Arg).re

def manuscriptNormP5_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-18774355590913 / 20000000000000000) (0 / 1) (-4) (0) (12321 / 10000) (0 / 1)

private theorem manuscriptNormP5_4_arg_eq : manuscriptNormP5_4Arg = barrierComplex (111 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_4_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-18774355590913 / 20000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_4_exact_interval :
    manuscriptNormP5_4Term ∈ Set.Icc (manuscriptNormP5_4Interval.1 : ℝ) (manuscriptNormP5_4Interval.2 : ℝ) := by
  unfold manuscriptNormP5_4Term
  rw [manuscriptNormP5_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-18774355590913 / 20000000000000000) (0 / 1)
    manuscriptNormP5_4Arg (-4) (0) (12321 / 10000) (111 / 400) (0 / 1)
  have hratio : ((0 / 1) / (111 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_4_rounded_endpoints :
    (75210910163037250886802437 / 62500000000000000000000000000) ≤ manuscriptNormP5_4Interval.1 ∧ manuscriptNormP5_4Interval.2 ≤ (1203374562608596014442386537 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP5_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_4_enclosure :
    manuscriptNormP5_4Term ∈ Set.Icc ((75210910163037250886802437 / 62500000000000000000000000000) : ℝ) ((1203374562608596014442386537 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((75210910163037250886802437 / 62500000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_4_rounded_endpoints.1
  have hhi : (manuscriptNormP5_4Interval.2 : ℝ) ≤ ((1203374562608596014442386537 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_4_exact_interval.1, manuscriptNormP5_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
