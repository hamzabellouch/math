import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY17

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y17YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-3) (0) (36481 / 20000) (0 / 1)

private theorem manuscriptCase2Y17YV3_arg_eq : barrierCase2Y17YV3LogArg = barrierComplex (191 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV3LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV3Interval.1 : ℝ) (manuscriptCase2Y17YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y17YV3LogArg).re ∈ _
  rw [manuscriptCase2Y17YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y17YV3LogArg (-3) (0) (36481 / 20000) (191 / 400) (0 / 1)
  have hratio : ((0 / 1) / (191 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV3_rounded_endpoints :
    (-9115398115950183808995127702261925257 / 250000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV3Interval.1 ∧ manuscriptCase2Y17YV3Interval.2 ≤ (-364615924638007352259647075624043434879 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-9115398115950183808995127702261925257 / 250000000000000000000000000000000000000) : ℝ) ((-364615924638007352259647075624043434879 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-9115398115950183808995127702261925257 / 250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV3Interval.2 : ℝ) ≤ ((-364615924638007352259647075624043434879 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV3_exact_interval.1, manuscriptCase2Y17YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y17YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-3) (0) (473273378 / 244140625) (0 / 1)

private theorem manuscriptCase2Y17YV4_arg_eq : barrierCase2Y17YV4LogArg = barrierComplex (15383 / 31250) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV4LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV4Interval.1 : ℝ) (manuscriptCase2Y17YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y17YV4LogArg).re ∈ _
  rw [manuscriptCase2Y17YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y17YV4LogArg (-3) (0) (473273378 / 244140625) (15383 / 31250) (0 / 1)
  have hratio : ((0 / 1) / (15383 / 31250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV4_rounded_endpoints :
    (823444281171949695506353877833458949573 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV4Interval.1 ∧ manuscriptCase2Y17YV4Interval.2 ≤ (823444281171949695757682221355933906007 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((823444281171949695506353877833458949573 / 10000000000000000000000000000000000000000) : ℝ) ((823444281171949695757682221355933906007 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((823444281171949695506353877833458949573 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV4Interval.2 : ℝ) ≤ ((823444281171949695757682221355933906007 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV4_exact_interval.1, manuscriptCase2Y17YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y17YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (4757033 / 3125000) (979 / 2925)

private theorem manuscriptCase2Y17YV5_arg_eq : barrierCase2Y17YV5LogArg = barrierComplex (979 / 2500) (-117 / 100) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV5LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV5Interval.1 : ℝ) (manuscriptCase2Y17YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y17YV5LogArg).re ∈ _
  rw [manuscriptCase2Y17YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y17YV5LogArg (0) (-2) (4757033 / 3125000) (117 / 50) (979 / 1250)
  have hratio : ((979 / 1250) / (117 / 50) : ℚ) = (979 / 2925) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV5_rounded_endpoints :
    (-536986466772285346270205359776662456329 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV5Interval.1 ∧ manuscriptCase2Y17YV5Interval.2 ≤ (-10488016929146197624878418345388590513 / 39062500000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-536986466772285346270205359776662456329 / 2000000000000000000000000000000000000000) : ℝ) ((-10488016929146197624878418345388590513 / 39062500000000000000000000000000000000) : ℝ) := by
  have hlo : ((-536986466772285346270205359776662456329 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV5Interval.2 : ℝ) ≤ ((-10488016929146197624878418345388590513 / 39062500000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV5_exact_interval.1, manuscriptCase2Y17YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
