import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY11

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y11YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-8) (0) (1069291766441791201 / 610351562500000000) (0 / 1)

private theorem manuscriptCase2Y11YV3_arg_eq : barrierCase2Y11YV3LogArg = barrierComplex (1034065649 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV3LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV3Interval.1 : ℝ) (manuscriptCase2Y11YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y11YV3LogArg).re ∈ _
  rw [manuscriptCase2Y11YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y11YV3LogArg (-8) (0) (1069291766441791201 / 610351562500000000) (1034065649 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (1034065649 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV3_rounded_endpoints :
    (-1229326030777019344597910059148376418201 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV3Interval.1 ∧ manuscriptCase2Y11YV3Interval.2 ≤ (-614663015388509672165714431546041280221 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-1229326030777019344597910059148376418201 / 10000000000000000000000000000000000000000) : ℝ) ((-614663015388509672165714431546041280221 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1229326030777019344597910059148376418201 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV3Interval.2 : ℝ) ≤ ((-614663015388509672165714431546041280221 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV3_exact_interval.1, manuscriptCase2Y11YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y11YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-8) (0) (42404995720765419889 / 23841857910156250000) (0 / 1)

private theorem manuscriptCase2Y11YV4_arg_eq : barrierCase2Y11YV4LogArg = barrierComplex (6511911833 / 78125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV4LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV4Interval.1 : ℝ) (manuscriptCase2Y11YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y11YV4LogArg).re ∈ _
  rw [manuscriptCase2Y11YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y11YV4LogArg (-8) (0) (42404995720765419889 / 23841857910156250000) (6511911833 / 78125000000) (0 / 1)
  have hratio : ((0 / 1) / (6511911833 / 78125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV4_rounded_endpoints :
    (2886736769646175359771970487883452409253 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV4Interval.1 ∧ manuscriptCase2Y11YV4Interval.2 ≤ (72168419241154384009992646988623252179 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((2886736769646175359771970487883452409253 / 10000000000000000000000000000000000000000) : ℝ) ((72168419241154384009992646988623252179 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((2886736769646175359771970487883452409253 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV4Interval.2 : ℝ) ≤ ((72168419241154384009992646988623252179 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV4_exact_interval.1, manuscriptCase2Y11YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y11YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (2329860883151481722761 / 1953125000000000000000) (12237500000 / 46691588931)

private theorem manuscriptCase2Y11YV5_arg_eq : barrierCase2Y11YV5LogArg = barrierComplex (979 / 2500) (-46691588931 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV5LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV5Interval.1 : ℝ) (manuscriptCase2Y11YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y11YV5LogArg).re ∈ _
  rw [manuscriptCase2Y11YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y11YV5LogArg (1) (-2) (2329860883151481722761 / 1953125000000000000000) (46691588931 / 15625000000) (979 / 1250)
  have hratio : ((979 / 1250) / (46691588931 / 15625000000) : ℚ) = (12237500000 / 46691588931) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV5_rounded_endpoints :
    (-623810145153093738342409170749172462497 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV5Interval.1 ∧ manuscriptCase2Y11YV5Interval.2 ≤ (-3119050725765468552237929691811794334101 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-623810145153093738342409170749172462497 / 2000000000000000000000000000000000000000) : ℝ) ((-3119050725765468552237929691811794334101 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-623810145153093738342409170749172462497 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV5Interval.2 : ℝ) ≤ ((-3119050725765468552237929691811794334101 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV5_exact_interval.1, manuscriptCase2Y11YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
