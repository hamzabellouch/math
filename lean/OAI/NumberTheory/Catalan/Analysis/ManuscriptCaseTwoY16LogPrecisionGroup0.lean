import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY16

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y16YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (2) (0) (3721 / 2500) (0 / 1)

private theorem manuscriptCase2Y16YV0_arg_eq : barrierCase2Y16YV0LogArg = barrierComplex (61 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV0LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV0Interval.1 : ℝ) (manuscriptCase2Y16YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y16YV0LogArg).re ∈ _
  rw [manuscriptCase2Y16YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y16YV0LogArg (2) (0) (3721 / 2500) (61 / 25) (0 / 1)
  have hratio : ((0 / 1) / (61 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV0_rounded_endpoints :
    (-1355766641098466786098688609693048362817 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV0Interval.1 ∧ manuscriptCase2Y16YV0Interval.2 ≤ (-677883320549233392946711684202067333647 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1355766641098466786098688609693048362817 / 10000000000000000000000000000000000000000) : ℝ) ((-677883320549233392946711684202067333647 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1355766641098466786098688609693048362817 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV0Interval.2 : ℝ) ≤ ((-677883320549233392946711684202067333647 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV0_exact_interval.1, manuscriptCase2Y16YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y16YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (3243601 / 3125000) (0 / 1)

private theorem manuscriptCase2Y16YV1_arg_eq : barrierCase2Y16YV1LogArg = barrierComplex (1801 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV1LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV1Interval.1 : ℝ) (manuscriptCase2Y16YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y16YV1LogArg).re ∈ _
  rw [manuscriptCase2Y16YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y16YV1LogArg (3) (0) (3243601 / 3125000) (1801 / 625) (0 / 1)
  have hratio : ((0 / 1) / (1801 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV1_rounded_endpoints :
    (-471139731525183842090014372909969637003 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV1Interval.1 ∧ manuscriptCase2Y16YV1Interval.2 ≤ (-94227946305036768399966975088317085049 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-471139731525183842090014372909969637003 / 10000000000000000000000000000000000000000) : ℝ) ((-94227946305036768399966975088317085049 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-471139731525183842090014372909969637003 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV1Interval.2 : ℝ) ≤ ((-94227946305036768399966975088317085049 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV1_exact_interval.1, manuscriptCase2Y16YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y16YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-1) (0) (624962 / 390625) (0 / 1)

private theorem manuscriptCase2Y16YV2_arg_eq : barrierCase2Y16YV2LogArg = barrierComplex (559 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV2LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV2Interval.1 : ℝ) (manuscriptCase2Y16YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y16YV2LogArg).re ∈ _
  rw [manuscriptCase2Y16YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y16YV2LogArg (-1) (0) (624962 / 390625) (559 / 625) (0 / 1)
  have hratio : ((0 / 1) / (559 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV2_rounded_endpoints :
    (28407195706569381060130386714337977369 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV2Interval.1 ∧ manuscriptCase2Y16YV2Interval.2 ≤ (2840719570656938107731819784827108947 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((28407195706569381060130386714337977369 / 10000000000000000000000000000000000000000) : ℝ) ((2840719570656938107731819784827108947 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((28407195706569381060130386714337977369 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV2Interval.2 : ℝ) ≤ ((2840719570656938107731819784827108947 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV2_exact_interval.1, manuscriptCase2Y16YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
