import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX4

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X4XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (1) (0) (3564840283053506201809 / 3200000000000000000000) (0 / 1)

private theorem manuscriptCase2X4XV3_arg_eq : barrierCase2X4XV3LogArg = barrierComplex (59706283447 / 40000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV3LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV3Interval.1 : ℝ) (manuscriptCase2X4XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X4XV3LogArg).re ∈ _
  rw [manuscriptCase2X4XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X4XV3LogArg (1) (0) (3564840283053506201809 / 3200000000000000000000) (59706283447 / 40000000000) (0 / 1)
  have hratio : ((0 / 1) / (59706283447 / 40000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV3_rounded_endpoints :
    (-12348781737937104394982084395315540781 / 625000000000000000000000000000000000000) ≤ manuscriptCase2X4XV3Interval.1 ∧ manuscriptCase2X4XV3Interval.2 ≤ (-49395126951748417571601439011030305749 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-12348781737937104394982084395315540781 / 625000000000000000000000000000000000000) : ℝ) ((-49395126951748417571601439011030305749 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-12348781737937104394982084395315540781 / 625000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV3Interval.2 : ℝ) ≤ ((-49395126951748417571601439011030305749 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV3_exact_interval.1, manuscriptCase2X4XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (1) (0) (142560808500174391488001 / 125000000000000000000000) (0 / 1)

private theorem manuscriptCase2X4XV4_arg_eq : barrierCase2X4XV4LogArg = barrierComplex (377572255999 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV4LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV4Interval.1 : ℝ) (manuscriptCase2X4XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X4XV4LogArg).re ∈ _
  rw [manuscriptCase2X4XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X4XV4LogArg (1) (0) (142560808500174391488001 / 125000000000000000000000) (377572255999 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (377572255999 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV4_rounded_endpoints :
    (479017820388466871868815368762755670501 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XV4Interval.1 ∧ manuscriptCase2X4XV4Interval.2 ≤ (95803564077693374389453386865103858731 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((479017820388466871868815368762755670501 / 10000000000000000000000000000000000000000) : ℝ) ((95803564077693374389453386865103858731 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((479017820388466871868815368762755670501 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV4Interval.2 : ℝ) ≤ ((95803564077693374389453386865103858731 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV4_exact_interval.1, manuscriptCase2X4XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (11636181442364052445849 / 10000000000000000000000) (40449739707 / 100000000000)

private theorem manuscriptCase2X4XV5_arg_eq : barrierCase2X4XV5LogArg = barrierComplex (1 / 1) (40449739707 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV5LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV5Interval.1 : ℝ) (manuscriptCase2X4XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X4XV5LogArg).re ∈ _
  rw [manuscriptCase2X4XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X4XV5LogArg (0) (0) (11636181442364052445849 / 10000000000000000000000) (1 / 1) (40449739707 / 100000000000)
  have hratio : ((40449739707 / 100000000000) / (1 / 1) : ℚ) = (40449739707 / 100000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV5_rounded_endpoints :
    (-9933374652715381126409459601375769239 / 156250000000000000000000000000000000000) ≤ manuscriptCase2X4XV5Interval.1 ∧ manuscriptCase2X4XV5Interval.2 ≤ (-127147195554756878417611004347023769461 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-9933374652715381126409459601375769239 / 156250000000000000000000000000000000000) : ℝ) ((-127147195554756878417611004347023769461 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-9933374652715381126409459601375769239 / 156250000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV5Interval.2 : ℝ) ≤ ((-127147195554756878417611004347023769461 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV5_exact_interval.1, manuscriptCase2X4XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
