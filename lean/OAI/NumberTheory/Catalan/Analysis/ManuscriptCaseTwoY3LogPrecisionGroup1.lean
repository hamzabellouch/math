import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY3

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y3YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (1) (0) (27866371313463303190249 / 20000000000000000000000) (0 / 1)

private theorem manuscriptCase2Y3YV3_arg_eq : barrierCase2Y3YV3LogArg = barrierComplex (166932235693 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV3LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV3Interval.1 : ℝ) (manuscriptCase2Y3YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y3YV3LogArg).re ∈ _
  rw [manuscriptCase2Y3YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y3YV3LogArg (1) (0) (27866371313463303190249 / 20000000000000000000000) (166932235693 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (166932235693 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV3_rounded_endpoints :
    (252756931345347977781176055264173547197 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV3Interval.1 ∧ manuscriptCase2Y3YV3Interval.2 ≤ (63189232836336994453620912386308147019 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((252756931345347977781176055264173547197 / 10000000000000000000000000000000000000000) : ℝ) ((63189232836336994453620912386308147019 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((252756931345347977781176055264173547197 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV3Interval.2 : ℝ) ≤ ((63189232836336994453620912386308147019 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV3_exact_interval.1, manuscriptCase2Y3YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y3YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (1) (0) (1164690246957693264779161 / 781250000000000000000000) (0 / 1)

private theorem manuscriptCase2Y3YV4_arg_eq : barrierCase2Y3YV4LogArg = barrierComplex (1079208157381 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV4LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV4Interval.1 : ℝ) (manuscriptCase2Y3YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y3YV4LogArg).re ∈ _
  rw [manuscriptCase2Y3YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y3YV4LogArg (1) (0) (1164690246957693264779161 / 781250000000000000000000) (1079208157381 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (1079208157381 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV4_rounded_endpoints :
    (-317310000045252579853969930624203841313 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV4Interval.1 ∧ manuscriptCase2Y3YV4Interval.2 ≤ (-634620000090505159629488295426729018217 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-317310000045252579853969930624203841313 / 5000000000000000000000000000000000000000) : ℝ) ((-634620000090505159629488295426729018217 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-317310000045252579853969930624203841313 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV4Interval.2 : ℝ) ≤ ((-634620000090505159629488295426729018217 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV4_exact_interval.1, manuscriptCase2Y3YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y3YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-3) (-1) (11875255648734120920689 / 7812500000000000000000) (50037220633 / 145762779367)

private theorem manuscriptCase2Y3YV5_arg_eq : barrierCase2Y3YV5LogArg = barrierComplex (979 / 2500) (-47862779367 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV5LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV5Interval.1 : ℝ) (manuscriptCase2Y3YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y3YV5LogArg).re ∈ _
  rw [manuscriptCase2Y3YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y3YV5LogArg (-3) (-1) (11875255648734120920689 / 7812500000000000000000) (145762779367 / 250000000000) (50037220633 / 250000000000)
  have hratio : ((50037220633 / 250000000000) / (145762779367 / 250000000000) : ℚ) = (50037220633 / 145762779367) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV5_rounded_endpoints :
    (256730190771947416959416118397066762283 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV5Interval.1 ∧ manuscriptCase2Y3YV5Interval.2 ≤ (64182547692986871731596636940417739323 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((256730190771947416959416118397066762283 / 10000000000000000000000000000000000000000) : ℝ) ((64182547692986871731596636940417739323 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((256730190771947416959416118397066762283 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV5Interval.2 : ℝ) ≤ ((64182547692986871731596636940417739323 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV5_exact_interval.1, manuscriptCase2Y3YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
