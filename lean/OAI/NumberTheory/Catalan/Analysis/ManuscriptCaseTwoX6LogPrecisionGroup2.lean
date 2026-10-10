import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX6

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X6XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-1) (0) (22048628153053442329 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2X6XV0_arg_eq : barrierCase2X6XV0LogArg = barrierComplex (4695596677 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV0LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV0Interval.1 : ℝ) (manuscriptCase2X6XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X6XV0LogArg).re ∈ _
  rw [manuscriptCase2X6XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X6XV0LogArg (-1) (0) (22048628153053442329 / 19531250000000000000) (4695596677 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (4695596677 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV0_rounded_endpoints :
    (-434630970593567501655513925056277717309 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X6XV0Interval.1 ∧ manuscriptCase2X6XV0Interval.2 ≤ (-217315485296783750776440652279070178853 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-434630970593567501655513925056277717309 / 10000000000000000000000000000000000000000) : ℝ) ((-217315485296783750776440652279070178853 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-434630970593567501655513925056277717309 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV0Interval.2 : ℝ) ≤ ((-217315485296783750776440652279070178853 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV0_exact_interval.1, manuscriptCase2X6XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-2) (0) (120160840683730980961 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2X6XV1_arg_eq : barrierCase2X6XV1LogArg = barrierComplex (10961790031 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV1LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV1Interval.1 : ℝ) (manuscriptCase2X6XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X6XV1LogArg).re ∈ _
  rw [manuscriptCase2X6XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X6XV1LogArg (-2) (0) (120160840683730980961 / 61035156250000000000) (10961790031 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (10961790031 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV1_rounded_endpoints :
    (-157792099219252048166596992612581680913 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X6XV1Interval.1 ∧ manuscriptCase2X6XV1Interval.2 ≤ (-157792099219252048092880575154398783069 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-157792099219252048166596992612581680913 / 10000000000000000000000000000000000000000) : ℝ) ((-157792099219252048092880575154398783069 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-157792099219252048166596992612581680913 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV1Interval.2 : ℝ) ≤ ((-157792099219252048092880575154398783069 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV1_exact_interval.1, manuscriptCase2X6XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (0) (0) (6335911101681966521809 / 3906250000000000000000) (0 / 1)

private theorem manuscriptCase2X6XV2_arg_eq : barrierCase2X6XV2LogArg = barrierComplex (79598436553 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV2LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV2Interval.1 : ℝ) (manuscriptCase2X6XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X6XV2LogArg).re ∈ _
  rw [manuscriptCase2X6XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X6XV2LogArg (0) (0) (6335911101681966521809 / 3906250000000000000000) (79598436553 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (79598436553 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV2_rounded_endpoints :
    (15388705982820171826206299516026455267 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X6XV2Interval.1 ∧ manuscriptCase2X6XV2Interval.2 ≤ (61554823931280687304825253451343789347 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((15388705982820171826206299516026455267 / 2500000000000000000000000000000000000000) : ℝ) ((61554823931280687304825253451343789347 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((15388705982820171826206299516026455267 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV2Interval.2 : ℝ) ≤ ((61554823931280687304825253451343789347 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV2_exact_interval.1, manuscriptCase2X6XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
