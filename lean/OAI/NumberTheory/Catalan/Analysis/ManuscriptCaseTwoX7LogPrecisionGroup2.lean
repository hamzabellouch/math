import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX7

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X7XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-1) (0) (27207063757111793569 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2X7XV0_arg_eq : barrierCase2X7XV0LogArg = barrierComplex (5216039087 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV0LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV0Interval.1 : ℝ) (manuscriptCase2X7XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X7XV0LogArg).re ∈ _
  rw [manuscriptCase2X7XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X7XV0LogArg (-1) (0) (27207063757111793569 / 19531250000000000000) (5216039087 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (5216039087 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV0_rounded_endpoints :
    (-34358414075435057106905848354464684491 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X7XV0Interval.1 ∧ manuscriptCase2X7XV0Interval.2 ≤ (-54973462520696091350522833267436914413 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-34358414075435057106905848354464684491 / 1250000000000000000000000000000000000000) : ℝ) ((-54973462520696091350522833267436914413 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-34358414075435057106905848354464684491 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV0Interval.2 : ℝ) ≤ ((-54973462520696091350522833267436914413 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV0_exact_interval.1, manuscriptCase2X7XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-1) (0) (156828465932756142121 / 122070312500000000000) (0 / 1)

private theorem manuscriptCase2X7XV1_arg_eq : barrierCase2X7XV1LogArg = barrierComplex (12523117261 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV1LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV1Interval.1 : ℝ) (manuscriptCase2X7XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X7XV1LogArg).re ∈ _
  rw [manuscriptCase2X7XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X7XV1LogArg (-1) (0) (156828465932756142121 / 122070312500000000000) (12523117261 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (12523117261 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV1_rounded_endpoints :
    (-12314180659739346454114368168446554719 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X7XV1Interval.1 ∧ manuscriptCase2X7XV1Interval.2 ≤ (-49256722638957385801427556429055514809 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-12314180659739346454114368168446554719 / 1250000000000000000000000000000000000000) : ℝ) ((-49256722638957385801427556429055514809 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-12314180659739346454114368168446554719 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV1Interval.2 : ℝ) ≤ ((-49256722638957385801427556429055514809 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV1_exact_interval.1, manuscriptCase2X7XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (0) (0) (5457304350898027021849 / 3906250000000000000000) (0 / 1)

private theorem manuscriptCase2X7XV2_arg_eq : barrierCase2X7XV2LogArg = barrierComplex (73873570043 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV2LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV2Interval.1 : ℝ) (manuscriptCase2X7XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X7XV2LogArg).re ∈ _
  rw [manuscriptCase2X7XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X7XV2LogArg (0) (0) (5457304350898027021849 / 3906250000000000000000) (73873570043 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (73873570043 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV2_rounded_endpoints :
    (42556143224545614504297724681206949077 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X7XV2Interval.1 ∧ manuscriptCase2X7XV2Interval.2 ≤ (21278071612272807252148862340649025719 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((42556143224545614504297724681206949077 / 10000000000000000000000000000000000000000) : ℝ) ((21278071612272807252148862340649025719 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((42556143224545614504297724681206949077 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV2Interval.2 : ℝ) ≤ ((21278071612272807252148862340649025719 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV2_exact_interval.1, manuscriptCase2X7XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
