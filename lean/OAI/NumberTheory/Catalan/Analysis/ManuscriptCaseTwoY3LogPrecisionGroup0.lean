import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY3

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y3YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (1) (0) (131727284847239067009 / 78125000000000000000) (0 / 1)

private theorem manuscriptCase2Y3YV0_arg_eq : barrierCase2Y3YV0LogArg = barrierComplex (11477250753 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV0LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV0Interval.1 : ℝ) (manuscriptCase2Y3YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y3YV0LogArg).re ∈ _
  rw [manuscriptCase2Y3YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y3YV0LogArg (1) (0) (131727284847239067009 / 78125000000000000000) (11477250753 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (11477250753 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV0_rounded_endpoints :
    (-57736617474763721399436986573838932813 / 625000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV0Interval.1 ∧ manuscriptCase2Y3YV0Interval.2 ≤ (-92378587959621954228835401362850378531 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-57736617474763721399436986573838932813 / 625000000000000000000000000000000000000) : ℝ) ((-92378587959621954228835401362850378531 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-57736617474763721399436986573838932813 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV0Interval.2 : ℝ) ≤ ((-92378587959621954228835401362850378531 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV0_exact_interval.1, manuscriptCase2Y3YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y3YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (2) (0) (1136145147849601603081 / 976562500000000000000) (0 / 1)

private theorem manuscriptCase2Y3YV1_arg_eq : barrierCase2Y3YV1LogArg = barrierComplex (33706752259 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV1LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV1Interval.1 : ℝ) (manuscriptCase2Y3YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y3YV1LogArg).re ∈ _
  rw [manuscriptCase2Y3YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y3YV1LogArg (2) (0) (1136145147849601603081 / 976562500000000000000) (33706752259 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (33706752259 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV1_rounded_endpoints :
    (-342255342397023897790403717071333379361 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV1Interval.1 ∧ manuscriptCase2Y3YV1Interval.2 ≤ (-171127671198511948865142026046205285761 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-342255342397023897790403717071333379361 / 10000000000000000000000000000000000000000) : ℝ) ((-171127671198511948865142026046205285761 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-342255342397023897790403717071333379361 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV1Interval.2 : ℝ) ≤ ((-171127671198511948865142026046205285761 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV1_exact_interval.1, manuscriptCase2Y3YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y3YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (1) (0) (9486807086530027108089 / 7812500000000000000000) (0 / 1)

private theorem manuscriptCase2Y3YV2_arg_eq : barrierCase2Y3YV2LogArg = barrierComplex (97400241717 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV2LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV2Interval.1 : ℝ) (manuscriptCase2Y3YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y3YV2LogArg).re ∈ _
  rw [manuscriptCase2Y3YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y3YV2LogArg (1) (0) (9486807086530027108089 / 7812500000000000000000) (97400241717 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (97400241717 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV2_rounded_endpoints :
    (-56464835631229278218527220452819068159 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV2Interval.1 ∧ manuscriptCase2Y3YV2Interval.2 ≤ (-112929671262458556419866649582080759631 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-56464835631229278218527220452819068159 / 5000000000000000000000000000000000000000) : ℝ) ((-112929671262458556419866649582080759631 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-56464835631229278218527220452819068159 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV2Interval.2 : ℝ) ≤ ((-112929671262458556419866649582080759631 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV2_exact_interval.1, manuscriptCase2Y3YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
