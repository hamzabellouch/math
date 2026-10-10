import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX15

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X15XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (1) (0) (109100922483127967401 / 78125000000000000000) (0 / 1)

private theorem manuscriptCase2X15XV0_arg_eq : barrierCase2X15XV0LogArg = barrierComplex (10445138701 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV0LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV0Interval.1 : ℝ) (manuscriptCase2X15XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X15XV0LogArg).re ∈ _
  rw [manuscriptCase2X15XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X15XV0LogArg (1) (0) (109100922483127967401 / 78125000000000000000) (10445138701 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (10445138701 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV0_rounded_endpoints :
    (780563400223913858821734312333108063539 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV0Interval.1 ∧ manuscriptCase2X15XV0Interval.2 ≤ (19514085005597846473109173320794136341 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((780563400223913858821734312333108063539 / 10000000000000000000000000000000000000000) : ℝ) ((19514085005597846473109173320794136341 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((780563400223913858821734312333108063539 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV0Interval.2 : ℝ) ≤ ((19514085005597846473109173320794136341 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV0_exact_interval.1, manuscriptCase2X15XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (1) (0) (795827576704401706609 / 488281250000000000000) (0 / 1)

private theorem manuscriptCase2X15XV1_arg_eq : barrierCase2X15XV1LogArg = barrierComplex (28210416103 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV1LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV1Interval.1 : ℝ) (manuscriptCase2X15XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X15XV1LogArg).re ∈ _
  rw [manuscriptCase2X15XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X15XV1LogArg (1) (0) (795827576704401706609 / 488281250000000000000) (28210416103 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (28210416103 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV1_rounded_endpoints :
    (263012684498551412102380562424761248383 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV1Interval.1 ∧ manuscriptCase2X15XV1Interval.2 ≤ (65753171124637853033110133269760894271 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((263012684498551412102380562424761248383 / 10000000000000000000000000000000000000000) : ℝ) ((65753171124637853033110133269760894271 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((263012684498551412102380562424761248383 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV1Interval.2 : ℝ) ≤ ((65753171124637853033110133269760894271 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV1_exact_interval.1, manuscriptCase2X15XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-4) (0) (267436121320984055521 / 244140625000000000000) (0 / 1)

private theorem manuscriptCase2X15XV2_arg_eq : barrierCase2X15XV2LogArg = barrierComplex (16353474289 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV2LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV2Interval.1 : ℝ) (manuscriptCase2X15XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X15XV2LogArg).re ∈ _
  rw [manuscriptCase2X15XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X15XV2LogArg (-4) (0) (267436121320984055521 / 244140625000000000000) (16353474289 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (16353474289 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV2_rounded_endpoints :
    (-68253635110602016471221924566343844363 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV2Interval.1 ∧ manuscriptCase2X15XV2Interval.2 ≤ (-34126817555301008228735845753748971507 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-68253635110602016471221924566343844363 / 2000000000000000000000000000000000000000) : ℝ) ((-34126817555301008228735845753748971507 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-68253635110602016471221924566343844363 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV2Interval.2 : ℝ) ≤ ((-34126817555301008228735845753748971507 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV2_exact_interval.1, manuscriptCase2X15XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
