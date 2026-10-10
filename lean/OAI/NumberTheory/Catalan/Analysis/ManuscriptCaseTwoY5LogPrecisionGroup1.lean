import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY5

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y5YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (0) (0) (273631175658813137881 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2Y5YV3_arg_eq : barrierCase2Y5YV3LogArg = barrierComplex (16541800859 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV3LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV3Interval.1 : ℝ) (manuscriptCase2Y5YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y5YV3LogArg).re ∈ _
  rw [manuscriptCase2Y5YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y5YV3LogArg (0) (0) (273631175658813137881 / 156250000000000000000) (16541800859 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (16541800859 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV3_rounded_endpoints :
    (138193620411112699001588260664996054907 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV3Interval.1 ∧ manuscriptCase2Y5YV3Interval.2 ≤ (17274202551389087375201025394649047949 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((138193620411112699001588260664996054907 / 10000000000000000000000000000000000000000) : ℝ) ((17274202551389087375201025394649047949 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((138193620411112699001588260664996054907 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV3Interval.2 : ℝ) ≤ ((17274202551389087375201025394649047949 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV3_exact_interval.1, manuscriptCase2Y5YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y5YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (0) (0) (11428484972509162314409 / 6103515625000000000000) (0 / 1)

private theorem manuscriptCase2Y5YV4_arg_eq : barrierCase2Y5YV4LogArg = barrierComplex (106904092403 / 78125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV4LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV4Interval.1 : ℝ) (manuscriptCase2Y5YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y5YV4LogArg).re ∈ _
  rw [manuscriptCase2Y5YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y5YV4LogArg (0) (0) (11428484972509162314409 / 6103515625000000000000) (106904092403 / 78125000000) (0 / 1)
  have hratio : ((0 / 1) / (106904092403 / 78125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV4_rounded_endpoints :
    (-182185476955752973050258599264263512377 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV4Interval.1 ∧ manuscriptCase2Y5YV4Interval.2 ≤ (-182185476955752973049028590318429342911 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-182185476955752973050258599264263512377 / 5000000000000000000000000000000000000000) : ℝ) ((-182185476955752973049028590318429342911 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-182185476955752973050258599264263512377 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV4Interval.2 : ℝ) ≤ ((-182185476955752973049028590318429342911 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV4_exact_interval.1, manuscriptCase2Y5YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y5YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-2) (-1) (370573685748216330241 / 244140625000000000000) (-2622421921 / 27097421921)

private theorem manuscriptCase2Y5YV5_arg_eq : barrierCase2Y5YV5LogArg = barrierComplex (979 / 2500) (-14859921921 / 31250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV5LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV5Interval.1 : ℝ) (manuscriptCase2Y5YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y5YV5LogArg).re ∈ _
  rw [manuscriptCase2Y5YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y5YV5LogArg (-2) (-1) (370573685748216330241 / 244140625000000000000) (27097421921 / 31250000000) (-2622421921 / 31250000000)
  have hratio : ((-2622421921 / 31250000000) / (27097421921 / 31250000000) : ℚ) = (-2622421921 / 27097421921) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV5_rounded_endpoints :
    (-32358298622241884624768924430220501079 / 312500000000000000000000000000000000000) ≤ manuscriptCase2Y5YV5Interval.1 ∧ manuscriptCase2Y5YV5Interval.2 ≤ (-517732777955870119058800253347293920913 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-32358298622241884624768924430220501079 / 312500000000000000000000000000000000000) : ℝ) ((-517732777955870119058800253347293920913 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-32358298622241884624768924430220501079 / 312500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV5Interval.2 : ℝ) ≤ ((-517732777955870119058800253347293920913 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV5_exact_interval.1, manuscriptCase2Y5YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
