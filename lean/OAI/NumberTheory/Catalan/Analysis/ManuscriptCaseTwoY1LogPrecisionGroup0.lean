import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY1

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y1YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (1) (0) (27987535463172038209 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2Y1YV0_arg_eq : barrierCase2Y1YV0LogArg = barrierComplex (5290324703 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV0LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV0Interval.1 : ℝ) (manuscriptCase2Y1YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y1YV0LogArg).re ∈ _
  rw [manuscriptCase2Y1YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y1YV0LogArg (1) (0) (27987535463172038209 / 19531250000000000000) (5290324703 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (5290324703 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV0_rounded_endpoints :
    (-800155382280272217410859335500917078157 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV0Interval.1 ∧ manuscriptCase2Y1YV0Interval.2 ≤ (-25004855696258506790882084843594721743 / 312500000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-800155382280272217410859335500917078157 / 10000000000000000000000000000000000000000) : ℝ) ((-25004855696258506790882084843594721743 / 312500000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-800155382280272217410859335500917078157 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV0Interval.2 : ℝ) ≤ ((-25004855696258506790882084843594721743 / 312500000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV0_exact_interval.1, manuscriptCase2Y1YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y1YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (1) (0) (240512769189523343881 / 122070312500000000000) (0 / 1)

private theorem manuscriptCase2Y1YV1_arg_eq : barrierCase2Y1YV1LogArg = barrierComplex (15508474109 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV1LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV1Interval.1 : ℝ) (manuscriptCase2Y1YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y1YV1LogArg).re ∈ _
  rw [manuscriptCase2Y1YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y1YV1LogArg (1) (0) (240512769189523343881 / 122070312500000000000) (15508474109 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (15508474109 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV1_rounded_endpoints :
    (-1192317806065728970261061965133153941 / 39062500000000000000000000000000000000) ≤ manuscriptCase2Y1YV1Interval.1 ∧ manuscriptCase2Y1YV1Interval.2 ≤ (-305233358352826616342613357023022051581 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-1192317806065728970261061965133153941 / 39062500000000000000000000000000000000) : ℝ) ((-305233358352826616342613357023022051581 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1192317806065728970261061965133153941 / 39062500000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV1Interval.2 : ℝ) ≤ ((-305233358352826616342613357023022051581 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV1_exact_interval.1, manuscriptCase2Y1YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y1YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (1) (0) (2876330097958366623289 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y1YV2_arg_eq : barrierCase2Y1YV2LogArg = barrierComplex (53631428267 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV2LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV2Interval.1 : ℝ) (manuscriptCase2Y1YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y1YV2LogArg).re ∈ _
  rw [manuscriptCase2Y1YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y1YV2LogArg (1) (0) (2876330097958366623289 / 1953125000000000000000) (53631428267 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (53631428267 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV2_rounded_endpoints :
    (-137480985100092153900560224876390420969 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV2Interval.1 ∧ manuscriptCase2Y1YV2Interval.2 ≤ (-137480985100092153883372433534403111253 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-137480985100092153900560224876390420969 / 10000000000000000000000000000000000000000) : ℝ) ((-137480985100092153883372433534403111253 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-137480985100092153900560224876390420969 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV2Interval.2 : ℝ) ≤ ((-137480985100092153883372433534403111253 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV2_exact_interval.1, manuscriptCase2Y1YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
