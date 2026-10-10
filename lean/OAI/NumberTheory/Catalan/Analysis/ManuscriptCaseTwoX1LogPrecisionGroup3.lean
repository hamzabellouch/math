import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX1

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X1XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (1) (0) (8551812141988655690089 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X1XV3_arg_eq : barrierCase2X1XV3LogArg = barrierComplex (92476008467 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV3LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV3Interval.1 : ℝ) (manuscriptCase2X1XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X1XV3LogArg).re ∈ _
  rw [manuscriptCase2X1XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X1XV3LogArg (1) (0) (8551812141988655690089 / 5000000000000000000000) (92476008467 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (92476008467 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV3_rounded_endpoints :
    (-15166030333520509697337096378299075871 / 500000000000000000000000000000000000000) ≤ manuscriptCase2X1XV3Interval.1 ∧ manuscriptCase2X1XV3Interval.2 ≤ (-303320606670410193913429982871798731471 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-15166030333520509697337096378299075871 / 500000000000000000000000000000000000000) : ℝ) ((-303320606670410193913429982871798731471 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-15166030333520509697337096378299075871 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV3Interval.2 : ℝ) ≤ ((-303320606670410193913429982871798731471 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV3_exact_interval.1, manuscriptCase2X1XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (1) (0) (345128362336659132784921 / 195312500000000000000000) (0 / 1)

private theorem manuscriptCase2X1XV4_arg_eq : barrierCase2X1XV4LogArg = barrierComplex (587476265339 / 312500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV4LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV4Interval.1 : ℝ) (manuscriptCase2X1XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X1XV4LogArg).re ∈ _
  rw [manuscriptCase2X1XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X1XV4LogArg (1) (0) (345128362336659132784921 / 195312500000000000000000) (587476265339 / 312500000000) (0 / 1)
  have hratio : ((0 / 1) / (587476265339 / 312500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV4_rounded_endpoints :
    (146674904733949244463660752219956483251 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X1XV4Interval.1 ∧ manuscriptCase2X1XV4Interval.2 ≤ (733374523669746222396837667852216546937 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((146674904733949244463660752219956483251 / 2000000000000000000000000000000000000000) : ℝ) ((733374523669746222396837667852216546937 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((146674904733949244463660752219956483251 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV4Interval.2 : ℝ) ≤ ((733374523669746222396837667852216546937 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV4_exact_interval.1, manuscriptCase2X1XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (1) (23226676953279903890929 / 15625000000000000000000) (-37812403673 / 212187596327)

private theorem manuscriptCase2X1XV5_arg_eq : barrierCase2X1XV5LogArg = barrierComplex (1 / 1) (87187596327 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV5LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV5Interval.1 : ℝ) (manuscriptCase2X1XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X1XV5LogArg).re ∈ _
  rw [manuscriptCase2X1XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X1XV5LogArg (0) (1) (23226676953279903890929 / 15625000000000000000000) (212187596327 / 125000000000) (-37812403673 / 125000000000)
  have hratio : ((-37812403673 / 125000000000) / (212187596327 / 125000000000) : ℚ) = (-37812403673 / 212187596327) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV5_rounded_endpoints :
    (-900873746403146392829049670209078365713 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X1XV5Interval.1 ∧ manuscriptCase2X1XV5Interval.2 ≤ (-900873746403146323137973919881737118621 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-900873746403146392829049670209078365713 / 10000000000000000000000000000000000000000) : ℝ) ((-900873746403146323137973919881737118621 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-900873746403146392829049670209078365713 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV5Interval.2 : ℝ) ≤ ((-900873746403146323137973919881737118621 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV5_exact_interval.1, manuscriptCase2X1XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
