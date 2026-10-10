import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY10

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y10YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-5) (0) (465967520114798050561 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2Y10YV3_arg_eq : barrierCase2Y10YV3LogArg = barrierComplex (21586280831 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV3LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV3Interval.1 : ℝ) (manuscriptCase2Y10YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y10YV3LogArg).re ∈ _
  rw [manuscriptCase2Y10YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y10YV3LogArg (-5) (0) (465967520114798050561 / 312500000000000000000) (21586280831 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (21586280831 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV3_rounded_endpoints :
    (-756228146121110296231633701052435954669 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV3Interval.1 ∧ manuscriptCase2Y10YV3Interval.2 ≤ (-756228146121110296065095729535905607111 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-756228146121110296231633701052435954669 / 10000000000000000000000000000000000000000) : ℝ) ((-756228146121110296065095729535905607111 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-756228146121110296231633701052435954669 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV3Interval.2 : ℝ) ≤ ((-756228146121110296065095729535905607111 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV3_exact_interval.1, manuscriptCase2Y10YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y10YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-5) (0) (19122559885948297082929 / 12207031250000000000000) (0 / 1)

private theorem manuscriptCase2Y10YV4_arg_eq : barrierCase2Y10YV4LogArg = barrierComplex (138284344327 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV4LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV4Interval.1 : ℝ) (manuscriptCase2Y10YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y10YV4LogArg).re ∈ _
  rw [manuscriptCase2Y10YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y10YV4LogArg (-5) (0) (19122559885948297082929 / 12207031250000000000000) (138284344327 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (138284344327 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV4_rounded_endpoints :
    (350505766206370252900672807168141356267 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV4Interval.1 ∧ manuscriptCase2Y10YV4Interval.2 ≤ (350505766206370252979124376221288834753 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((350505766206370252900672807168141356267 / 2000000000000000000000000000000000000000) : ℝ) ((350505766206370252979124376221288834753 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((350505766206370252900672807168141356267 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV4Interval.2 : ℝ) ≤ ((350505766206370252979124376221288834753 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV4_exact_interval.1, manuscriptCase2Y10YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y10YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (129441949333299867963721 / 125000000000000000000000) (8900000000 / 31473134199)

private theorem manuscriptCase2Y10YV5_arg_eq : barrierCase2Y10YV5LogArg = barrierComplex (979 / 2500) (-346204476189 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV5LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV5Interval.1 : ℝ) (manuscriptCase2Y10YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y10YV5LogArg).re ∈ _
  rw [manuscriptCase2Y10YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y10YV5LogArg (1) (-2) (129441949333299867963721 / 125000000000000000000000) (346204476189 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (346204476189 / 125000000000) : ℚ) = (8900000000 / 31473134199) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV5_rounded_endpoints :
    (-1492849301137716218100485224206855642367 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV5Interval.1 ∧ manuscriptCase2Y10YV5Interval.2 ≤ (-59713972045508645934537085728581045081 / 200000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-1492849301137716218100485224206855642367 / 5000000000000000000000000000000000000000) : ℝ) ((-59713972045508645934537085728581045081 / 200000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1492849301137716218100485224206855642367 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV5Interval.2 : ℝ) ≤ ((-59713972045508645934537085728581045081 / 200000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV5_exact_interval.1, manuscriptCase2Y10YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
