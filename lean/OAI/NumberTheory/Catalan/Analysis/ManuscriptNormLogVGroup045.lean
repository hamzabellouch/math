import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV10_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV10_5Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV10_5Arg).re

def manuscriptNormV10_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV10_5_arg_eq : manuscriptNormV10_5Arg = barrierComplex (2551 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_5_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_5_exact_interval :
    manuscriptNormV10_5Term ∈ Set.Icc (manuscriptNormV10_5Interval.1 : ℝ) (manuscriptNormV10_5Interval.2 : ℝ) := by
  unfold manuscriptNormV10_5Term
  rw [manuscriptNormV10_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (160081263898183 / 10000000000000000) (-16780401343011 / 10000000000000000)
    manuscriptNormV10_5Arg (-4) (0) (6507601 / 6250000) (2551 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (2551 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_5_rounded_endpoints :
    (-2733586989958455530919248339 / 125000000000000000000000000000) ≤ manuscriptNormV10_5Interval.1 ∧ manuscriptNormV10_5Interval.2 ≤ (-10934347959833822121515096977 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV10_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_5_enclosure :
    manuscriptNormV10_5Term ∈ Set.Icc ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_5_rounded_endpoints.1
  have hhi : (manuscriptNormV10_5Interval.2 : ℝ) ≤ ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_5_exact_interval.1, manuscriptNormV10_5_exact_interval.2.trans hhi⟩

def manuscriptNormV10_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV10_6Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV10_6Arg).re

def manuscriptNormV10_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) (1) (0) (304467601 / 200000000) (0 / 1)

private theorem manuscriptNormV10_6_arg_eq : manuscriptNormV10_6Arg = barrierComplex (17449 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_6_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_6_exact_interval :
    manuscriptNormV10_6Term ∈ Set.Icc (manuscriptNormV10_6Interval.1 : ℝ) (manuscriptNormV10_6Interval.2 : ℝ) := by
  unfold manuscriptNormV10_6Term
  rw [manuscriptNormV10_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-68919525805689 / 10000000000000000) (-145456838557667 / 10000000000000000)
    manuscriptNormV10_6Arg (1) (0) (304467601 / 200000000) (17449 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (17449 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_6_rounded_endpoints :
    (-3836731030965981801976136659 / 1000000000000000000000000000000) ≤ manuscriptNormV10_6Interval.1 ∧ manuscriptNormV10_6Interval.2 ≤ (-767346206193196360302151557 / 200000000000000000000000000000) := by
  simp only [manuscriptNormV10_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_6_enclosure :
    manuscriptNormV10_6Term ∈ Set.Icc ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-3836731030965981801976136659 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_6_rounded_endpoints.1
  have hhi : (manuscriptNormV10_6Interval.2 : ℝ) ≤ ((-767346206193196360302151557 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_6_exact_interval.1, manuscriptNormV10_6_exact_interval.2.trans hhi⟩

def manuscriptNormV10_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV10_7Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV10_7Arg).re

def manuscriptNormV10_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV10_7_arg_eq : manuscriptNormV10_7Arg = barrierComplex (281 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_7_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_7_exact_interval :
    manuscriptNormV10_7Term ∈ Set.Icc (manuscriptNormV10_7Interval.1 : ℝ) (manuscriptNormV10_7Interval.2 : ℝ) := by
  unfold manuscriptNormV10_7Term
  rw [manuscriptNormV10_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (37458406176029 / 10000000000000000) (143853215065837 / 10000000000000000)
    manuscriptNormV10_7Arg (-6) (0) (78961 / 62500) (281 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (281 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_7_rounded_endpoints :
    (-1837847806637300544349037963 / 250000000000000000000000000000) ≤ manuscriptNormV10_7Interval.1 ∧ manuscriptNormV10_7Interval.2 ≤ (-735139122654920217587852529 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV10_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_7_enclosure :
    manuscriptNormV10_7Term ∈ Set.Icc ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_7_rounded_endpoints.1
  have hhi : (manuscriptNormV10_7Interval.2 : ℝ) ≤ ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_7_exact_interval.1, manuscriptNormV10_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
