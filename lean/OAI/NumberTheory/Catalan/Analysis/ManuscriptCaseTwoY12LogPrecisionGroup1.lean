import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY12

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y12YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-10) (0) (11016982551984992361 / 9765625000000000000) (0 / 1)

private theorem manuscriptCase2Y12YV3_arg_eq : barrierCase2Y12YV3LogArg = barrierComplex (3319184019 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV3LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV3Interval.1 : ℝ) (manuscriptCase2Y12YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y12YV3LogArg).re ∈ _
  rw [manuscriptCase2Y12YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y12YV3LogArg (-10) (0) (11016982551984992361 / 9765625000000000000) (3319184019 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (3319184019 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV3_rounded_endpoints :
    (-83989222135646232279384013633507527893 / 500000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV3Interval.1 ∧ manuscriptCase2Y12YV3Interval.2 ≤ (-419946110678231161313651082465219065717 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-83989222135646232279384013633507527893 / 500000000000000000000000000000000000000) : ℝ) ((-419946110678231161313651082465219065717 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-83989222135646232279384013633507527893 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV3Interval.2 : ℝ) ≤ ((-419946110678231161313651082465219065717 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV3_exact_interval.1, manuscriptCase2Y12YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y12YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-10) (0) (401157961756300303129 / 381469726562500000000) (0 / 1)

private theorem manuscriptCase2Y12YV4_arg_eq : barrierCase2Y12YV4LogArg = barrierComplex (20028928123 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV4LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV4Interval.1 : ℝ) (manuscriptCase2Y12YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y12YV4LogArg).re ∈ _
  rw [manuscriptCase2Y12YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y12YV4LogArg (-10) (0) (401157961756300303129 / 381469726562500000000) (20028928123 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (20028928123 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV4_rounded_endpoints :
    (399731290772060408638547928687291293113 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV4Interval.1 ∧ manuscriptCase2Y12YV4Interval.2 ≤ (199865645386030204358499747125027458133 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((399731290772060408638547928687291293113 / 1000000000000000000000000000000000000000) : ℝ) ((199865645386030204358499747125027458133 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((399731290772060408638547928687291293113 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV4Interval.2 : ℝ) ≤ ((199865645386030204358499747125027458133 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV4_exact_interval.1, manuscriptCase2Y12YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y12YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (156810173640480608513521 / 125000000000000000000000) (97900000000 / 383700095961)

private theorem manuscriptCase2Y12YV5_arg_eq : barrierCase2Y12YV5LogArg = barrierComplex (979 / 2500) (-383700095961 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV5LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV5Interval.1 : ℝ) (manuscriptCase2Y12YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y12YV5LogArg).re ∈ _
  rw [manuscriptCase2Y12YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y12YV5LogArg (1) (-2) (156810173640480608513521 / 125000000000000000000000) (383700095961 / 125000000000) (979 / 1250)
  have hratio : ((979 / 1250) / (383700095961 / 125000000000) : ℚ) = (97900000000 / 383700095961) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV5_rounded_endpoints :
    (-49466368766657137613859049814788137709 / 156250000000000000000000000000000000000) ≤ manuscriptCase2Y12YV5Interval.1 ∧ manuscriptCase2Y12YV5Interval.2 ≤ (-3165847601066056667812863026213289630871 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-49466368766657137613859049814788137709 / 156250000000000000000000000000000000000) : ℝ) ((-3165847601066056667812863026213289630871 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-49466368766657137613859049814788137709 / 156250000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV5Interval.2 : ℝ) ≤ ((-3165847601066056667812863026213289630871 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV5_exact_interval.1, manuscriptCase2Y12YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
