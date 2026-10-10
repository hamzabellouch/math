import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX8

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X8XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-1) (0) (1859865375311428969 / 1220703125000000000) (0 / 1)

private theorem manuscriptCase2X8XV0_arg_eq : barrierCase2X8XV0LogArg = barrierComplex (1363768813 / 1562500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV0LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV0Interval.1 : ℝ) (manuscriptCase2X8XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X8XV0LogArg).re ∈ _
  rw [manuscriptCase2X8XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X8XV0LogArg (-1) (0) (1859865375311428969 / 1220703125000000000) (1363768813 / 1562500000) (0 / 1)
  have hratio : ((0 / 1) / (1363768813 / 1562500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV0_rounded_endpoints :
    (-103381271043387819811243606279641571089 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X8XV0Interval.1 ∧ manuscriptCase2X8XV0Interval.2 ≤ (-206762542086775639519854589765004352199 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-103381271043387819811243606279641571089 / 5000000000000000000000000000000000000000) : ℝ) ((-206762542086775639519854589765004352199 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-103381271043387819811243606279641571089 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV0Interval.2 : ℝ) ≤ ((-206762542086775639519854589765004352199 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV0_exact_interval.1, manuscriptCase2X8XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-1) (0) (10956473629365360721 / 7629394531250000000) (0 / 1)

private theorem manuscriptCase2X8XV1_arg_eq : barrierCase2X8XV1LogArg = barrierComplex (3310056439 / 3906250000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV1LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV1Interval.1 : ℝ) (manuscriptCase2X8XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X8XV1LogArg).re ∈ _
  rw [manuscriptCase2X8XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X8XV1LogArg (-1) (0) (10956473629365360721 / 7629394531250000000) (3310056439 / 3906250000) (0 / 1)
  have hratio : ((0 / 1) / (3310056439 / 3906250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV1_rounded_endpoints :
    (-73725129232854442595849441438120638939 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X8XV1Interval.1 ∧ manuscriptCase2X8XV1Interval.2 ≤ (-73725129232854442565789608945834124581 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-73725129232854442595849441438120638939 / 10000000000000000000000000000000000000000) : ℝ) ((-73725129232854442565789608945834124581 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-73725129232854442595849441438120638939 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV1Interval.2 : ℝ) ≤ ((-73725129232854442565789608945834124581 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV1_exact_interval.1, manuscriptCase2X8XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (0) (0) (317233254778307905249 / 244140625000000000000) (0 / 1)

private theorem manuscriptCase2X8XV2_arg_eq : barrierCase2X8XV2LogArg = barrierComplex (17811043057 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV2LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV2Interval.1 : ℝ) (manuscriptCase2X8XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X8XV2LogArg).re ∈ _
  rw [manuscriptCase2X8XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X8XV2LogArg (0) (0) (317233254778307905249 / 244140625000000000000) (17811043057 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (17811043057 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV2_rounded_endpoints :
    (8332771801945721107466774264241110303 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X8XV2Interval.1 ∧ manuscriptCase2X8XV2Interval.2 ≤ (16665543603891442214933548528482226701 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((8332771801945721107466774264241110303 / 2500000000000000000000000000000000000000) : ℝ) ((16665543603891442214933548528482226701 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((8332771801945721107466774264241110303 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV2Interval.2 : ℝ) ≤ ((16665543603891442214933548528482226701 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV2_exact_interval.1, manuscriptCase2X8XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
