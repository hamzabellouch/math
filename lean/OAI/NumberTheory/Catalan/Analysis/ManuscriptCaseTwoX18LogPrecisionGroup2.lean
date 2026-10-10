import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX18

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X18XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-5) (0) (32 / 25) (0 / 1)

private theorem manuscriptCase2X18XV0_arg_eq : barrierCase2X18XV0LogArg = barrierComplex (1 / 5) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV0LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV0Interval.1 : ℝ) (manuscriptCase2X18XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X18XV0LogArg).re ∈ _
  rw [manuscriptCase2X18XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X18XV0LogArg (-5) (0) (32 / 25) (1 / 5) (0 / 1)
  have hratio : ((0 / 1) / (1 / 5) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV0_rounded_endpoints :
    (-611554660562135379719212065567230061573 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X18XV0Interval.1 ∧ manuscriptCase2X18XV0Interval.2 ≤ (-1223109321124270759181842579889116719967 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-611554660562135379719212065567230061573 / 2500000000000000000000000000000000000000) : ℝ) ((-1223109321124270759181842579889116719967 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-611554660562135379719212065567230061573 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV0Interval.2 : ℝ) ≤ ((-1223109321124270759181842579889116719967 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV0_exact_interval.1, manuscriptCase2X18XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-10) (0) (1024 / 625) (0 / 1)

private theorem manuscriptCase2X18XV1_arg_eq : barrierCase2X18XV1LogArg = barrierComplex (1 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV1LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV1Interval.1 : ℝ) (manuscriptCase2X18XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X18XV1LogArg).re ∈ _
  rw [manuscriptCase2X18XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X18XV1LogArg (-10) (0) (1024 / 625) (1 / 25) (0 / 1)
  have hratio : ((0 / 1) / (1 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV1_rounded_endpoints :
    (-358233679807110607090274278683753497911 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X18XV1Interval.1 ∧ manuscriptCase2X18XV1Interval.2 ≤ (-716467359614221214030249293919428709027 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-358233679807110607090274278683753497911 / 2500000000000000000000000000000000000000) : ℝ) ((-716467359614221214030249293919428709027 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-358233679807110607090274278683753497911 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV1Interval.2 : ℝ) ≤ ((-716467359614221214030249293919428709027 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV1_exact_interval.1, manuscriptCase2X18XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (1) (0) (2209 / 1250) (0 / 1)

private theorem manuscriptCase2X18XV2_arg_eq : barrierCase2X18XV2LogArg = barrierComplex (47 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV2LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV2Interval.1 : ℝ) (manuscriptCase2X18XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X18XV2LogArg).re ∈ _
  rw [manuscriptCase2X18XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X18XV2LogArg (1) (0) (2209 / 1250) (47 / 25) (0 / 1)
  have hratio : ((0 / 1) / (47 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV2_rounded_endpoints :
    (160683791822971125598985710767462956619 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X18XV2Interval.1 ∧ manuscriptCase2X18XV2Interval.2 ≤ (20085473977871390702023954059620503921 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((160683791822971125598985710767462956619 / 10000000000000000000000000000000000000000) : ℝ) ((20085473977871390702023954059620503921 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((160683791822971125598985710767462956619 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV2Interval.2 : ℝ) ≤ ((20085473977871390702023954059620503921 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV2_exact_interval.1, manuscriptCase2X18XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
