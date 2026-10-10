import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP2_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP2_5Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP2_5Arg).re

def manuscriptNormP2_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) (-3) (0) (6561 / 5000) (0 / 1)

private theorem manuscriptNormP2_5_arg_eq : manuscriptNormP2_5Arg = barrierComplex (81 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_5_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_5_exact_interval :
    manuscriptNormP2_5Term ∈ Set.Icc (manuscriptNormP2_5Interval.1 : ℝ) (manuscriptNormP2_5Interval.2 : ℝ) := by
  unfold manuscriptNormP2_5Term
  rw [manuscriptNormP2_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (109898540610783 / 40000000000000000) (437141826370109 / 40000000000000000)
    manuscriptNormP2_5Arg (-3) (0) (6561 / 5000) (81 / 200) (0 / 1)
  have hratio : ((0 / 1) / (81 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_5_rounded_endpoints :
    (-620836233685038813724759441 / 250000000000000000000000000000) ≤ manuscriptNormP2_5Interval.1 ∧ manuscriptNormP2_5Interval.2 ≤ (-1241672467370077627171235311 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP2_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_5_enclosure :
    manuscriptNormP2_5Term ∈ Set.Icc ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-620836233685038813724759441 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_5_rounded_endpoints.1
  have hhi : (manuscriptNormP2_5Interval.2 : ℝ) ≤ ((-1241672467370077627171235311 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_5_exact_interval.1, manuscriptNormP2_5_exact_interval.2.trans hhi⟩

def manuscriptNormP2_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP2_6Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP2_6Arg).re

def manuscriptNormP2_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP2_6_arg_eq : manuscriptNormP2_6Arg = barrierComplex (411 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_6_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_6_exact_interval :
    manuscriptNormP2_6Term ∈ Set.Icc (manuscriptNormP2_6Interval.1 : ℝ) (manuscriptNormP2_6Interval.2 : ℝ) := by
  unfold manuscriptNormP2_6Term
  rw [manuscriptNormP2_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-249342691992771 / 20000000000000000) (-244406797738203 / 20000000000000000)
    manuscriptNormP2_6Arg (1) (0) (16918021 / 12500000) (411 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (411 / 250) : ℚ) = (-161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_6_rounded_endpoints :
    (-6685833039281012505245132349 / 1000000000000000000000000000000) ≤ manuscriptNormP2_6Interval.1 ∧ manuscriptNormP2_6Interval.2 ≤ (-6685833039281012504403289509 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP2_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_6_enclosure :
    manuscriptNormP2_6Term ∈ Set.Icc ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_6_rounded_endpoints.1
  have hhi : (manuscriptNormP2_6Interval.2 : ℝ) ≤ ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_6_exact_interval.1, manuscriptNormP2_6_exact_interval.2.trans hhi⟩

def manuscriptNormP2_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP2_7Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP2_7Arg).re

def manuscriptNormP2_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP2_7_arg_eq : manuscriptNormP2_7Arg = barrierComplex (89 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_7_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (284284403283 / 160000000000000) (69467599782309 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_7_exact_interval :
    manuscriptNormP2_7Term ∈ Set.Icc (manuscriptNormP2_7Interval.1 : ℝ) (manuscriptNormP2_7Interval.2 : ℝ) := by
  unfold manuscriptNormP2_7Term
  rw [manuscriptNormP2_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (284284403283 / 160000000000000) (69467599782309 / 4000000000000000)
    manuscriptNormP2_7Arg (-3) (0) (818021 / 781250) (89 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (89 / 250) : ℚ) = (-161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_7_rounded_endpoints :
    (1301547649377044894437730227 / 1000000000000000000000000000000) ≤ manuscriptNormP2_7Interval.1 ∧ manuscriptNormP2_7Interval.2 ≤ (1301547649377044894797660753 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP2_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_7_enclosure :
    manuscriptNormP2_7Term ∈ Set.Icc ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1301547649377044894437730227 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_7_rounded_endpoints.1
  have hhi : (manuscriptNormP2_7Interval.2 : ℝ) ≤ ((1301547649377044894797660753 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_7_exact_interval.1, manuscriptNormP2_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
