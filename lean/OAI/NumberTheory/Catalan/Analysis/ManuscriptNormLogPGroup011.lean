import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP3_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP3_4Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP3_4Arg).re

def manuscriptNormP3_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP3_4_arg_eq : manuscriptNormP3_4Arg = barrierComplex (81 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_4_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_4_exact_interval :
    manuscriptNormP3_4Term ∈ Set.Icc (manuscriptNormP3_4Interval.1 : ℝ) (manuscriptNormP3_4Interval.2 : ℝ) := by
  unfold manuscriptNormP3_4Term
  rw [manuscriptNormP3_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (109898540610783 / 40000000000000000) (-437141826370109 / 40000000000000000)
    manuscriptNormP3_4Arg (-3) (0) (6561 / 5000) (81 / 200) (0 / 1)
  have hratio : ((0 / 1) / (81 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_4_rounded_endpoints :
    (-620836233685038813724759441 / 250000000000000000000000000000) ≤ manuscriptNormP3_4Interval.1 ∧ manuscriptNormP3_4Interval.2 ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP3_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_4_enclosure :
    manuscriptNormP3_4Term ∈ Set.Icc ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_4_rounded_endpoints.1
  have hhi : (manuscriptNormP3_4Interval.2 : ℝ) ≤ ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_4_exact_interval.1, manuscriptNormP3_4_exact_interval.2.trans hhi⟩

def manuscriptNormP3_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP3_5Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP3_5Arg).re

def manuscriptNormP3_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP3_5_arg_eq : manuscriptNormP3_5Arg = barrierComplex (319 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_5_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_5_exact_interval :
    manuscriptNormP3_5Term ∈ Set.Icc (manuscriptNormP3_5Interval.1 : ℝ) (manuscriptNormP3_5Interval.2 : ℝ) := by
  unfold manuscriptNormP3_5Term
  rw [manuscriptNormP3_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-273161078429227 / 40000000000000000) (358543847837271 / 40000000000000000)
    manuscriptNormP3_5Arg (1) (0) (101761 / 80000) (319 / 200) (0 / 1)
  have hratio : ((0 / 1) / (319 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_5_rounded_endpoints :
    (-127531733280728920730965549 / 40000000000000000000000000000) ≤ manuscriptNormP3_5Interval.1 ∧ manuscriptNormP3_5Interval.2 ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP3_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_5_enclosure :
    manuscriptNormP3_5Term ∈ Set.Icc ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_5_rounded_endpoints.1
  have hhi : (manuscriptNormP3_5Interval.2 : ℝ) ≤ ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_5_exact_interval.1, manuscriptNormP3_5_exact_interval.2.trans hhi⟩

def manuscriptNormP3_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP3_6Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP3_6Arg).re

def manuscriptNormP3_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP3_6_arg_eq : manuscriptNormP3_6Arg = barrierComplex (89 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_6_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_6_exact_interval :
    manuscriptNormP3_6Term ∈ Set.Icc (manuscriptNormP3_6Interval.1 : ℝ) (manuscriptNormP3_6Interval.2 : ℝ) := by
  unfold manuscriptNormP3_6Term
  rw [manuscriptNormP3_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (284284403283 / 160000000000000) (-69467599782309 / 4000000000000000)
    manuscriptNormP3_6Arg (-3) (0) (818021 / 781250) (89 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (89 / 250) : ℚ) = (161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_6_rounded_endpoints :
    (1301547649377044894437730227 / 1000000000000000000000000000000) ≤ manuscriptNormP3_6Interval.1 ∧ manuscriptNormP3_6Interval.2 ≤ (1301547649377044894797660753 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP3_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_6_enclosure :
    manuscriptNormP3_6Term ∈ Set.Icc ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_6_rounded_endpoints.1
  have hhi : (manuscriptNormP3_6Interval.2 : ℝ) ≤ ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_6_exact_interval.1, manuscriptNormP3_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
