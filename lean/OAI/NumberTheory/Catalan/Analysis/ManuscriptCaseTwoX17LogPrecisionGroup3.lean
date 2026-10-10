import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX17

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X17XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (-8) (0) (240686114744316061921 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2X17XV3_arg_eq : barrierCase2X17XV3LogArg = barrierComplex (15514061839 / 200000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV3LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV3Interval.1 : ℝ) (manuscriptCase2X17XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X17XV3LogArg).re ∈ _
  rw [manuscriptCase2X17XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X17XV3LogArg (-8) (0) (240686114744316061921 / 156250000000000000000) (15514061839 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (15514061839 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV3_rounded_endpoints :
    (315265669036961290981136535375362129083 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X17XV3Interval.1 ∧ manuscriptCase2X17XV3Interval.2 ≤ (630531338073922582095503448813810158949 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((315265669036961290981136535375362129083 / 2500000000000000000000000000000000000000) : ℝ) ((630531338073922582095503448813810158949 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((315265669036961290981136535375362129083 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV3Interval.2 : ℝ) ≤ ((630531338073922582095503448813810158949 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV3_exact_interval.1, manuscriptCase2X17XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (-9) (0) (3102077283744758173969 / 3051757812500000000000) (0 / 1)

private theorem manuscriptCase2X17XV4_arg_eq : barrierCase2X17XV4LogArg = barrierComplex (55696295063 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV4LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV4Interval.1 : ℝ) (manuscriptCase2X17XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X17XV4LogArg).re ∈ _
  rw [manuscriptCase2X17XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X17XV4LogArg (-9) (0) (3102077283744758173969 / 3051757812500000000000) (55696295063 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (55696295063 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV4_rounded_endpoints :
    (-361439144957034813794405695667406934757 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV4Interval.1 ∧ manuscriptCase2X17XV4Interval.2 ≤ (-3614391449570348137237992866609196739193 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-361439144957034813794405695667406934757 / 1000000000000000000000000000000000000000) : ℝ) ((-3614391449570348137237992866609196739193 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-361439144957034813794405695667406934757 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV4Interval.2 : ℝ) ≤ ((-3614391449570348137237992866609196739193 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV4_exact_interval.1, manuscriptCase2X17XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (-1) (393399801544815802576681 / 250000000000000000000000) (121318337459 / 878681662541)

private theorem manuscriptCase2X17XV5_arg_eq : barrierCase2X17XV5LogArg = barrierComplex (1 / 1) (-378681662541 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV5LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV5Interval.1 : ℝ) (manuscriptCase2X17XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X17XV5LogArg).re ∈ _
  rw [manuscriptCase2X17XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X17XV5LogArg (0) (-1) (393399801544815802576681 / 250000000000000000000000) (878681662541 / 500000000000) (121318337459 / 500000000000)
  have hratio : ((121318337459 / 500000000000) / (878681662541 / 500000000000) : ℚ) = (121318337459 / 878681662541) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV5_rounded_endpoints :
    (155481916692865964192852906786952949627 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV5Interval.1 ∧ manuscriptCase2X17XV5Interval.2 ≤ (310963833385731942323920969448847910703 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((155481916692865964192852906786952949627 / 1000000000000000000000000000000000000000) : ℝ) ((310963833385731942323920969448847910703 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((155481916692865964192852906786952949627 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV5Interval.2 : ℝ) ≤ ((310963833385731942323920969448847910703 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV5_exact_interval.1, manuscriptCase2X17XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
