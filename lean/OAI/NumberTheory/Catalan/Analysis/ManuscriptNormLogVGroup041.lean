import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV9_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV9_6Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV9_6Arg).re

def manuscriptNormV9_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (160081263898183 / 10000000000000000) (16780401343011 / 10000000000000000) (-4) (0) (6507601 / 6250000) (0 / 1)

private theorem manuscriptNormV9_6_arg_eq : manuscriptNormV9_6Arg = barrierComplex (2551 / 10000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_6_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (160081263898183 / 10000000000000000) (16780401343011 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_6_exact_interval :
    manuscriptNormV9_6Term ∈ Set.Icc (manuscriptNormV9_6Interval.1 : ℝ) (manuscriptNormV9_6Interval.2 : ℝ) := by
  unfold manuscriptNormV9_6Term
  rw [manuscriptNormV9_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (160081263898183 / 10000000000000000) (16780401343011 / 10000000000000000)
    manuscriptNormV9_6Arg (-4) (0) (6507601 / 6250000) (2551 / 10000) (0 / 1)
  have hratio : ((0 / 1) / (2551 / 10000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_6_rounded_endpoints :
    (-2733586989958455530919248339 / 125000000000000000000000000000) ≤ manuscriptNormV9_6Interval.1 ∧ manuscriptNormV9_6Interval.2 ≤ (-10934347959833822121515096977 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV9_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_6_enclosure :
    manuscriptNormV9_6Term ∈ Set.Icc ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2733586989958455530919248339 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_6_rounded_endpoints.1
  have hhi : (manuscriptNormV9_6Interval.2 : ℝ) ≤ ((-10934347959833822121515096977 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_6_exact_interval.1, manuscriptNormV9_6_exact_interval.2.trans hhi⟩

def manuscriptNormV9_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV9_7Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV9_7Arg).re

def manuscriptNormV9_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-142349837215793 / 10000000000000000) (-42818261555831 / 10000000000000000) (1) (0) (13830961 / 8000000) (0 / 1)

private theorem manuscriptNormV9_7_arg_eq : manuscriptNormV9_7Arg = barrierComplex (3719 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_7_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-142349837215793 / 10000000000000000) (-42818261555831 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_7_exact_interval :
    manuscriptNormV9_7Term ∈ Set.Icc (manuscriptNormV9_7Interval.1 : ℝ) (manuscriptNormV9_7Interval.2 : ℝ) := by
  unfold manuscriptNormV9_7Term
  rw [manuscriptNormV9_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-142349837215793 / 10000000000000000) (-42818261555831 / 10000000000000000)
    manuscriptNormV9_7Arg (1) (0) (13830961 / 8000000) (3719 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (3719 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_7_rounded_endpoints :
    (-2207517269453298436964373209 / 250000000000000000000000000000) ≤ manuscriptNormV9_7Interval.1 ∧ manuscriptNormV9_7Interval.2 ≤ (-4415034538906596873448011269 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV9_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_7_enclosure :
    manuscriptNormV9_7Term ∈ Set.Icc ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-2207517269453298436964373209 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_7_rounded_endpoints.1
  have hhi : (manuscriptNormV9_7Interval.2 : ℝ) ≤ ((-4415034538906596873448011269 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_7_exact_interval.1, manuscriptNormV9_7_exact_interval.2.trans hhi⟩

def manuscriptNormV9_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 9 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV9_8Term : ℝ :=
  (-((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV9_8Arg).re

def manuscriptNormV9_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV9_8_arg_eq : manuscriptNormV9_8Arg = barrierComplex (281 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV9_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV9_8_weight_eq :
    -((barrierV2Tail.getD 9 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV9_8_exact_interval :
    manuscriptNormV9_8Term ∈ Set.Icc (manuscriptNormV9_8Interval.1 : ℝ) (manuscriptNormV9_8Interval.2 : ℝ) := by
  unfold manuscriptNormV9_8Term
  rw [manuscriptNormV9_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000)
    manuscriptNormV9_8Arg (-6) (0) (78961 / 62500) (281 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (281 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV9_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV9_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV9_8_rounded_endpoints :
    (-1837847806637300544349037963 / 250000000000000000000000000000) ≤ manuscriptNormV9_8Interval.1 ∧ manuscriptNormV9_8Interval.2 ≤ (-735139122654920217587852529 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV9_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV9_8_enclosure :
    manuscriptNormV9_8Term ∈ Set.Icc ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV9_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_8_rounded_endpoints.1
  have hhi : (manuscriptNormV9_8Interval.2 : ℝ) ≤ ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV9_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV9_8_exact_interval.1, manuscriptNormV9_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
