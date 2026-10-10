import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX8

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X8XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (0) (0) (828051992221800857809 / 625000000000000000000) (0 / 1)

private theorem manuscriptCase2X8XV3_arg_eq : barrierCase2X8XV3LogArg = barrierComplex (28775892553 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV3LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV3Interval.1 : ℝ) (manuscriptCase2X8XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X8XV3LogArg).re ∈ _
  rw [manuscriptCase2X8XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X8XV3LogArg (0) (0) (828051992221800857809 / 625000000000000000000) (28775892553 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (28775892553 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV3_rounded_endpoints :
    (-1734587229509958126617155830244336441 / 250000000000000000000000000000000000000) ≤ manuscriptCase2X8XV3Interval.1 ∧ manuscriptCase2X8XV3Interval.2 ≤ (-69383489180398325064686233209773133667 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-1734587229509958126617155830244336441 / 250000000000000000000000000000000000000) : ℝ) ((-69383489180398325064686233209773133667 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1734587229509958126617155830244336441 / 250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV3Interval.2 : ℝ) ≤ ((-69383489180398325064686233209773133667 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV3_exact_interval.1, manuscriptCase2X8XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (0) (0) (32650298507533483872001 / 24414062500000000000000) (0 / 1)

private theorem manuscriptCase2X8XV4_arg_eq : barrierCase2X8XV4LogArg = barrierComplex (180693936001 / 156250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV4LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV4Interval.1 : ℝ) (manuscriptCase2X8XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X8XV4LogArg).re ∈ _
  rw [manuscriptCase2X8XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X8XV4LogArg (0) (0) (32650298507533483872001 / 24414062500000000000000) (180693936001 / 156250000000) (0 / 1)
  have hratio : ((0 / 1) / (180693936001 / 156250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV4_rounded_endpoints :
    (33773366645984911470929812895447671673 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X8XV4Interval.1 ∧ manuscriptCase2X8XV4Interval.2 ≤ (33773366645984911470929812895448176997 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((33773366645984911470929812895447671673 / 2000000000000000000000000000000000000000) : ℝ) ((33773366645984911470929812895448176997 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((33773366645984911470929812895447671673 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV4Interval.2 : ℝ) ≤ ((33773366645984911470929812895448176997 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV4_exact_interval.1, manuscriptCase2X8XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (3966320502808058461849 / 3906250000000000000000) (7750516293 / 62500000000)

private theorem manuscriptCase2X8XV5_arg_eq : barrierCase2X8XV5LogArg = barrierComplex (1 / 1) (7750516293 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV5LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV5Interval.1 : ℝ) (manuscriptCase2X8XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X8XV5LogArg).re ∈ _
  rw [manuscriptCase2X8XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X8XV5LogArg (0) (0) (3966320502808058461849 / 3906250000000000000000) (1 / 1) (7750516293 / 62500000000)
  have hratio : ((7750516293 / 62500000000) / (1 / 1) : ℚ) = (7750516293 / 62500000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV5_rounded_endpoints :
    (-113394987920339319093802395111547644641 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X8XV5Interval.1 ∧ manuscriptCase2X8XV5Interval.2 ≤ (-226789975840678638187604790223095289281 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-113394987920339319093802395111547644641 / 5000000000000000000000000000000000000000) : ℝ) ((-226789975840678638187604790223095289281 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-113394987920339319093802395111547644641 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV5Interval.2 : ℝ) ≤ ((-226789975840678638187604790223095289281 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV5_exact_interval.1, manuscriptCase2X8XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
