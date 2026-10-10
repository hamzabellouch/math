import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX9

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X9XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (0) (0) (49223891603666388961 / 39062500000000000000) (0 / 1)

private theorem manuscriptCase2X9XV0_arg_eq : barrierCase2X9XV0LogArg = barrierComplex (7015974031 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV0LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV0Interval.1 : ℝ) (manuscriptCase2X9XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X9XV0LogArg).re ∈ _
  rw [manuscriptCase2X9XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X9XV0LogArg (0) (0) (49223891603666388961 / 39062500000000000000) (7015974031 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (7015974031 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV0_rounded_endpoints :
    (175715175196935216135331645379297608691 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV0Interval.1 ∧ manuscriptCase2X9XV0Interval.2 ≤ (21964396899616902016916455672412201181 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((175715175196935216135331645379297608691 / 10000000000000000000000000000000000000000) : ℝ) ((21964396899616902016916455672412201181 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((175715175196935216135331645379297608691 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV0Interval.2 : ℝ) ≤ ((21964396899616902016916455672412201181 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV0_exact_interval.1, manuscriptCase2X9XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (0) (0) (321231136351747500649 / 244140625000000000000) (0 / 1)

private theorem manuscriptCase2X9XV1_arg_eq : barrierCase2X9XV1LogArg = barrierComplex (17922922093 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV1LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV1Interval.1 : ℝ) (manuscriptCase2X9XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X9XV1LogArg).re ∈ _
  rw [manuscriptCase2X9XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X9XV1LogArg (0) (0) (321231136351747500649 / 244140625000000000000) (17922922093 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (17922922093 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV1_rounded_endpoints :
    (61080480539219862512106628541167131087 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV1Interval.1 ∧ manuscriptCase2X9XV1Interval.2 ≤ (61080480539219862512106628541167248887 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((61080480539219862512106628541167131087 / 10000000000000000000000000000000000000000) : ℝ) ((61080480539219862512106628541167248887 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((61080480539219862512106628541167131087 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV1Interval.2 : ℝ) ≤ ((61080480539219862512106628541167248887 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV1_exact_interval.1, manuscriptCase2X9XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-1) (0) (2924028369531133064281 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X9XV2_arg_eq : barrierCase2X9XV2LogArg = barrierComplex (54074285659 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV2LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV2Interval.1 : ℝ) (manuscriptCase2X9XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X9XV2LogArg).re ∈ _
  rw [manuscriptCase2X9XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X9XV2LogArg (-1) (0) (2924028369531133064281 / 1953125000000000000000) (54074285659 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (54074285659 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV2_rounded_endpoints :
    (-18429673611784200945291082108733886679 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV2Interval.1 ∧ manuscriptCase2X9XV2Interval.2 ≤ (-36859347223568401873394372811026488719 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-18429673611784200945291082108733886679 / 5000000000000000000000000000000000000000) : ℝ) ((-36859347223568401873394372811026488719 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-18429673611784200945291082108733886679 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV2Interval.2 : ℝ) ≤ ((-36859347223568401873394372811026488719 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV2_exact_interval.1, manuscriptCase2X9XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
