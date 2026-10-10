import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY12

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y12YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (403546385839119072001 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y12YV0_arg_eq : barrierCase2Y12YV0LogArg = barrierComplex (20088463999 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV0LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV0Interval.1 : ℝ) (manuscriptCase2Y12YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y12YV0LogArg).re ∈ _
  rw [manuscriptCase2Y12YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y12YV0LogArg (3) (0) (403546385839119072001 / 312500000000000000000) (20088463999 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (20088463999 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV0_rounded_endpoints :
    (-887302774269882101148057142795642196217 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV0Interval.1 ∧ manuscriptCase2Y12YV0Interval.2 ≤ (-354921109707952840397643284819374456677 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-887302774269882101148057142795642196217 / 5000000000000000000000000000000000000000) : ℝ) ((-354921109707952840397643284819374456677 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-887302774269882101148057142795642196217 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV0Interval.2 : ℝ) ≤ ((-354921109707952840397643284819374456677 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV0_exact_interval.1, manuscriptCase2Y12YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y12YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (3545058279156421648009 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2Y12YV1_arg_eq : barrierCase2Y12YV1LogArg = barrierComplex (59540391997 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV1LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV1Interval.1 : ℝ) (manuscriptCase2Y12YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y12YV1LogArg).re ∈ _
  rw [manuscriptCase2Y12YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y12YV1LogArg (3) (0) (3545058279156421648009 / 1953125000000000000000) (59540391997 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (59540391997 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV1_rounded_endpoints :
    (-595535660439531223609613044900838601827 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV1Interval.1 ∧ manuscriptCase2Y12YV1Interval.2 ≤ (-595535660439531223519274526430286537487 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-595535660439531223609613044900838601827 / 10000000000000000000000000000000000000000) : ℝ) ((-595535660439531223519274526430286537487 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-595535660439531223609613044900838601827 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV1Interval.2 : ℝ) ≤ ((-595535660439531223519274526430286537487 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV1_exact_interval.1, manuscriptCase2Y12YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y12YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-10) (0) (7165772253707712121 / 3814697265625000000) (0 / 1)

private theorem manuscriptCase2Y12YV2_arg_eq : barrierCase2Y12YV2LogArg = barrierComplex (2676896011 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV2LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV2Interval.1 : ℝ) (manuscriptCase2Y12YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y12YV2LogArg).re ∈ _
  rw [manuscriptCase2Y12YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y12YV2LogArg (-10) (0) (7165772253707712121 / 3814697265625000000) (2676896011 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (2676896011 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV2_rounded_endpoints :
    (160385967738633654304335203379576096501 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV2Interval.1 ∧ manuscriptCase2Y12YV2Interval.2 ≤ (200482459673292067923549470142316757341 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((160385967738633654304335203379576096501 / 2000000000000000000000000000000000000000) : ℝ) ((200482459673292067923549470142316757341 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((160385967738633654304335203379576096501 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV2Interval.2 : ℝ) ≤ ((200482459673292067923549470142316757341 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV2_exact_interval.1, manuscriptCase2Y12YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
