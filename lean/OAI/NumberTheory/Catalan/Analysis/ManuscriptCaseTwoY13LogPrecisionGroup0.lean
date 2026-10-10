import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY13

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y13YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (16358348811182986969 / 12500000000000000000) (0 / 1)

private theorem manuscriptCase2Y13YV0_arg_eq : barrierCase2Y13YV0LogArg = barrierComplex (4044545563 / 1250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV0LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV0Interval.1 : ℝ) (manuscriptCase2Y13YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y13YV0LogArg).re ∈ _
  rw [manuscriptCase2Y13YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y13YV0LogArg (3) (0) (16358348811182986969 / 12500000000000000000) (4044545563 / 1250000000) (0 / 1)
  have hratio : ((0 / 1) / (4044545563 / 1250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV0_rounded_endpoints :
    (-89236516891369744149533545709855134849 / 500000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV0Interval.1 ∧ manuscriptCase2Y13YV0Interval.2 ≤ (-892365168913697441341386526351345211983 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-89236516891369744149533545709855134849 / 500000000000000000000000000000000000000) : ℝ) ((-892365168913697441341386526351345211983 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-89236516891369744149533545709855134849 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV0Interval.2 : ℝ) ≤ ((-892365168913697441341386526351345211983 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV0_exact_interval.1, manuscriptCase2Y13YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y13YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (143727409660836882721 / 78125000000000000000) (0 / 1)

private theorem manuscriptCase2Y13YV1_arg_eq : barrierCase2Y13YV1LogArg = barrierComplex (11988636689 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV1LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV1Interval.1 : ℝ) (manuscriptCase2Y13YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y13YV1LogArg).re ∈ _
  rw [manuscriptCase2Y13YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y13YV1LogArg (3) (0) (143727409660836882721 / 78125000000000000000) (11988636689 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (11988636689 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV1_rounded_endpoints :
    (-598537074096313250505210998746914696457 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV1Interval.1 ∧ manuscriptCase2Y13YV1Interval.2 ≤ (-74817134262039156301835423771432158477 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-598537074096313250505210998746914696457 / 10000000000000000000000000000000000000000) : ℝ) ((-74817134262039156301835423771432158477 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-598537074096313250505210998746914696457 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV1Interval.2 : ℝ) ≤ ((-74817134262039156301835423771432158477 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV1_exact_interval.1, manuscriptCase2Y13YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y13YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-12) (0) (57599427361423249 / 38146972656250000) (0 / 1)

private theorem manuscriptCase2Y13YV2_arg_eq : barrierCase2Y13YV2LogArg = barrierComplex (239998807 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV2LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV2Interval.1 : ℝ) (manuscriptCase2Y13YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y13YV2LogArg).re ∈ _
  rw [manuscriptCase2Y13YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y13YV2LogArg (-12) (0) (57599427361423249 / 38146972656250000) (239998807 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (239998807 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV2_rounded_endpoints :
    (1006157640995933294354093392809882911417 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV2Interval.1 ∧ manuscriptCase2Y13YV2Interval.2 ≤ (1006157640995933294560346888868924542883 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((1006157640995933294354093392809882911417 / 10000000000000000000000000000000000000000) : ℝ) ((1006157640995933294560346888868924542883 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1006157640995933294354093392809882911417 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV2Interval.2 : ℝ) ≤ ((1006157640995933294560346888868924542883 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV2_exact_interval.1, manuscriptCase2Y13YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
