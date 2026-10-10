import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV8_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV8_7Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV8_7Arg).re

def manuscriptNormV8_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-473406586612213 / 10000000000000000) (0 / 1) (-5) (0) (722 / 625) (0 / 1)

private theorem manuscriptNormV8_7_arg_eq : manuscriptNormV8_7Arg = barrierComplex (19 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_7_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-473406586612213 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_7_exact_interval :
    manuscriptNormV8_7Term ∈ Set.Icc (manuscriptNormV8_7Interval.1 : ℝ) (manuscriptNormV8_7Interval.2 : ℝ) := by
  unfold manuscriptNormV8_7Term
  rw [manuscriptNormV8_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-473406586612213 / 10000000000000000) (0 / 1)
    manuscriptNormV8_7Arg (-5) (0) (722 / 625) (19 / 100) (0 / 1)
  have hratio : ((0 / 1) / (19 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_7_rounded_endpoints :
    (7862010919018189014159228319 / 100000000000000000000000000000) ≤ manuscriptNormV8_7Interval.1 ∧ manuscriptNormV8_7Interval.2 ≤ (4913756824386368134848479063 / 62500000000000000000000000000) := by
  simp only [manuscriptNormV8_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_7_enclosure :
    manuscriptNormV8_7Term ∈ Set.Icc ((7862010919018189014159228319 / 100000000000000000000000000000) : ℝ) ((4913756824386368134848479063 / 62500000000000000000000000000) : ℝ) := by
  have hlo : ((7862010919018189014159228319 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_7_rounded_endpoints.1
  have hhi : (manuscriptNormV8_7Interval.2 : ℝ) ≤ ((4913756824386368134848479063 / 62500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_7_exact_interval.1, manuscriptNormV8_7_exact_interval.2.trans hhi⟩

def manuscriptNormV8_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV8_8Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV8_8Arg).re

def manuscriptNormV8_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) (1) (0) (32761 / 20000) (0 / 1)

private theorem manuscriptNormV8_8_arg_eq : manuscriptNormV8_8Arg = barrierComplex (181 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_8_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_8_exact_interval :
    manuscriptNormV8_8Term ∈ Set.Icc (manuscriptNormV8_8Interval.1 : ℝ) (manuscriptNormV8_8Interval.2 : ℝ) := by
  unfold manuscriptNormV8_8Term
  rw [manuscriptNormV8_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3545037307063 / 2000000000000000) (-118268659735503 / 2500000000000000)
    manuscriptNormV8_8Arg (1) (0) (32761 / 20000) (181 / 100) (0 / 1)
  have hratio : ((0 / 1) / (181 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_8_rounded_endpoints :
    (-1051682900895782370273743751 / 1000000000000000000000000000000) ≤ manuscriptNormV8_8Interval.1 ∧ manuscriptNormV8_8Interval.2 ≤ (-16432545326496599533657089 / 15625000000000000000000000000) := by
  simp only [manuscriptNormV8_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_8_enclosure :
    manuscriptNormV8_8Term ∈ Set.Icc ((-1051682900895782370273743751 / 1000000000000000000000000000000) : ℝ) ((-16432545326496599533657089 / 15625000000000000000000000000) : ℝ) := by
  have hlo : ((-1051682900895782370273743751 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_8_rounded_endpoints.1
  have hhi : (manuscriptNormV8_8Interval.2 : ℝ) ≤ ((-16432545326496599533657089 / 15625000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_8_exact_interval.1, manuscriptNormV8_8_exact_interval.2.trans hhi⟩

def manuscriptNormV8_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 8 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV8_9Term : ℝ :=
  (-((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV8_9Arg).re

def manuscriptNormV8_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) (-6) (0) (78961 / 62500) (0 / 1)

private theorem manuscriptNormV8_9_arg_eq : manuscriptNormV8_9Arg = barrierComplex (281 / 2000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV8_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV8_9_weight_eq :
    -((barrierV2Tail.getD 8 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV8_9_exact_interval :
    manuscriptNormV8_9Term ∈ Set.Icc (manuscriptNormV8_9Interval.1 : ℝ) (manuscriptNormV8_9Interval.2 : ℝ) := by
  unfold manuscriptNormV8_9Term
  rw [manuscriptNormV8_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (37458406176029 / 10000000000000000) (-143853215065837 / 10000000000000000)
    manuscriptNormV8_9Arg (-6) (0) (78961 / 62500) (281 / 2000) (0 / 1)
  have hratio : ((0 / 1) / (281 / 2000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV8_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV8_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV8_9_rounded_endpoints :
    (-1837847806637300544349037963 / 250000000000000000000000000000) ≤ manuscriptNormV8_9Interval.1 ∧ manuscriptNormV8_9Interval.2 ≤ (-735139122654920217587852529 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV8_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV8_9_enclosure :
    manuscriptNormV8_9Term ∈ Set.Icc ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-1837847806637300544349037963 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV8_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_9_rounded_endpoints.1
  have hhi : (manuscriptNormV8_9Interval.2 : ℝ) ≤ ((-735139122654920217587852529 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV8_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV8_9_exact_interval.1, manuscriptNormV8_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
