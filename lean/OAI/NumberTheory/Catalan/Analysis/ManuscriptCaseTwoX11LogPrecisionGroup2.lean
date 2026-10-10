import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX11

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X11XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (0) (0) (15421695163507517641 / 9765625000000000000) (0 / 1)

private theorem manuscriptCase2X11XV0_arg_eq : barrierCase2X11XV0LogArg = barrierComplex (3927046621 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV0LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV0Interval.1 : ℝ) (manuscriptCase2X11XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X11XV0LogArg).re ∈ _
  rw [manuscriptCase2X11XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X11XV0LogArg (0) (0) (15421695163507517641 / 9765625000000000000) (3927046621 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (3927046621 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV0_rounded_endpoints :
    (34723108868870720539070429100481444963 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV0Interval.1 ∧ manuscriptCase2X11XV0Interval.2 ≤ (347231088688707205390704334197046049691 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((34723108868870720539070429100481444963 / 1000000000000000000000000000000000000000) : ℝ) ((347231088688707205390704334197046049691 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((34723108868870720539070429100481444963 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV0Interval.2 : ℝ) ≤ ((347231088688707205390704334197046049691 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV0_exact_interval.1, manuscriptCase2X11XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (0) (0) (104420600649692658769 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2X11XV1_arg_eq : barrierCase2X11XV1LogArg = barrierComplex (10218639863 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV1LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV1Interval.1 : ℝ) (manuscriptCase2X11XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X11XV1LogArg).re ∈ _
  rw [manuscriptCase2X11XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X11XV1LogArg (0) (0) (104420600649692658769 / 61035156250000000000) (10218639863 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (10218639863 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV1_rounded_endpoints :
    (59760997089611321137299984670542696541 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV1Interval.1 ∧ manuscriptCase2X11XV1Interval.2 ≤ (29880498544805660568650991640582380717 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((59760997089611321137299984670542696541 / 5000000000000000000000000000000000000000) : ℝ) ((29880498544805660568650991640582380717 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((59760997089611321137299984670542696541 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV1Interval.2 : ℝ) ≤ ((29880498544805660568650991640582380717 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV1_exact_interval.1, manuscriptCase2X11XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-1) (0) (502992180715659634561 / 488281250000000000000) (0 / 1)

private theorem manuscriptCase2X11XV2_arg_eq : barrierCase2X11XV2LogArg = barrierComplex (22427487169 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV2LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV2Interval.1 : ℝ) (manuscriptCase2X11XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X11XV2LogArg).re ∈ _
  rw [manuscriptCase2X11XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X11XV2LogArg (-1) (0) (502992180715659634561 / 488281250000000000000) (22427487169 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (22427487169 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV2_rounded_endpoints :
    (-10554876647972315800282619118408086323 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X11XV2Interval.1 ∧ manuscriptCase2X11XV2Interval.2 ≤ (-84439013183778526385073161623707313897 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-10554876647972315800282619118408086323 / 1250000000000000000000000000000000000000) : ℝ) ((-84439013183778526385073161623707313897 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-10554876647972315800282619118408086323 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV2Interval.2 : ℝ) ≤ ((-84439013183778526385073161623707313897 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV2_exact_interval.1, manuscriptCase2X11XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
