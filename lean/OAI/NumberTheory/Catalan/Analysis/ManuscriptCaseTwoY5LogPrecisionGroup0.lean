import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY5

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y5YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (2) (0) (2763153650914302321 / 2441406250000000000) (0 / 1)

private theorem manuscriptCase2Y5YV0_arg_eq : barrierCase2Y5YV0LogArg = barrierComplex (1662273639 / 781250000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV0LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV0Interval.1 : ℝ) (manuscriptCase2Y5YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y5YV0LogArg).re ∈ _
  rw [manuscriptCase2Y5YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y5YV0LogArg (2) (0) (2763153650914302321 / 2441406250000000000) (1662273639 / 781250000) (0 / 1)
  have hratio : ((0 / 1) / (1662273639 / 781250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV0_rounded_endpoints :
    (-71725685173001912107010165966868333667 / 625000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV0Interval.1 ∧ manuscriptCase2Y5YV0Interval.2 ≤ (-573805481384015296753448707236809309733 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-71725685173001912107010165966868333667 / 625000000000000000000000000000000000000) : ℝ) ((-573805481384015296753448707236809309733 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-71725685173001912107010165966868333667 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV0Interval.2 : ℝ) ≤ ((-573805481384015296753448707236809309733 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV0_exact_interval.1, manuscriptCase2Y5YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y5YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (2) (0) (23972734457647470889 / 15258789062500000000) (0 / 1)

private theorem manuscriptCase2Y5YV1_arg_eq : barrierCase2Y5YV1LogArg = barrierComplex (4896195917 / 1953125000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV1LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV1Interval.1 : ℝ) (manuscriptCase2Y5YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y5YV1LogArg).re ∈ _
  rw [manuscriptCase2Y5YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y5YV1LogArg (2) (0) (23972734457647470889 / 15258789062500000000) (4896195917 / 1953125000) (0 / 1)
  have hratio : ((0 / 1) / (4896195917 / 1953125000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV1_rounded_endpoints :
    (-81824032138860055683340755846571486279 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV1Interval.1 ∧ manuscriptCase2Y5YV1Interval.2 ≤ (-409120160694300278356584105825622688607 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-81824032138860055683340755846571486279 / 2000000000000000000000000000000000000000) : ℝ) ((-409120160694300278356584105825622688607 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-81824032138860055683340755846571486279 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV1Interval.2 : ℝ) ≤ ((-409120160694300278356584105825622688607 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV1_exact_interval.1, manuscriptCase2Y5YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y5YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (0) (0) (93532882576668080841 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2Y5YV2_arg_eq : barrierCase2Y5YV2LogArg = barrierComplex (9671239971 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV2LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV2Interval.1 : ℝ) (manuscriptCase2Y5YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y5YV2LogArg).re ∈ _
  rw [manuscriptCase2Y5YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y5YV2LogArg (0) (0) (93532882576668080841 / 61035156250000000000) (9671239971 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (9671239971 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV2_rounded_endpoints :
    (-27163407548930162106936402772489252361 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV2Interval.1 ∧ manuscriptCase2Y5YV2Interval.2 ≤ (-10865363019572064842774560983291333067 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-27163407548930162106936402772489252361 / 5000000000000000000000000000000000000000) : ℝ) ((-10865363019572064842774560983291333067 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-27163407548930162106936402772489252361 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV2Interval.2 : ℝ) ≤ ((-10865363019572064842774560983291333067 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV2_exact_interval.1, manuscriptCase2Y5YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
