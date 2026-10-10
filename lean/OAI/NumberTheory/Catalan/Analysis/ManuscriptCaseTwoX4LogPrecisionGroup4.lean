import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX4

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X4XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (487133922966132970489 / 400000000000000000000) (9334555317 / 20000000000)

private theorem manuscriptCase2X4XV7_arg_eq : barrierCase2X4XV7LogArg = barrierComplex (1 / 1) (9334555317 / 20000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV7LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV7Interval.1 : ℝ) (manuscriptCase2X4XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X4XV7LogArg).re ∈ _
  rw [manuscriptCase2X4XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X4XV7LogArg (0) (0) (487133922966132970489 / 400000000000000000000) (1 / 1) (9334555317 / 20000000000)
  have hratio : ((9334555317 / 20000000000) / (1 / 1) : ℚ) = (9334555317 / 20000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV7_rounded_endpoints :
    (-203387790856599486454597295928538098251 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X4XV7Interval.1 ∧ manuscriptCase2X4XV7Interval.2 ≤ (-50846947714149871496532886286083271571 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-203387790856599486454597295928538098251 / 2500000000000000000000000000000000000000) : ℝ) ((-50846947714149871496532886286083271571 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-203387790856599486454597295928538098251 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV7Interval.2 : ℝ) ≤ ((-50846947714149871496532886286083271571 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV7_exact_interval.1, manuscriptCase2X4XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (199243612885524653042089 / 160000000000000000000000) (198100007283 / 400000000000)

private theorem manuscriptCase2X4XV9_arg_eq : barrierCase2X4XV9LogArg = barrierComplex (1 / 1) (198100007283 / 400000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV9LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV9Interval.1 : ℝ) (manuscriptCase2X4XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X4XV9LogArg).re ∈ _
  rw [manuscriptCase2X4XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X4XV9LogArg (0) (0) (199243612885524653042089 / 160000000000000000000000) (1 / 1) (198100007283 / 400000000000)
  have hratio : ((198100007283 / 400000000000) / (1 / 1) : ℚ) = (198100007283 / 400000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV9_rounded_endpoints :
    (47436066437472282493734561968360028397 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X4XV9Interval.1 ∧ manuscriptCase2X4XV9Interval.2 ≤ (118590166093680712997320754976898834903 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((47436066437472282493734561968360028397 / 2000000000000000000000000000000000000000) : ℝ) ((118590166093680712997320754976898834903 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((47436066437472282493734561968360028397 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV9Interval.2 : ℝ) ≤ ((118590166093680712997320754976898834903 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV9_exact_interval.1, manuscriptCase2X4XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (1) (78774680500674391488001 / 62500000000000000000000) (-122427744001 / 377572255999)

private theorem manuscriptCase2X4XV11_arg_eq : barrierCase2X4XV11LogArg = barrierComplex (1 / 1) (127572255999 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV11LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV11Interval.1 : ℝ) (manuscriptCase2X4XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X4XV11LogArg).re ∈ _
  rw [manuscriptCase2X4XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X4XV11LogArg (0) (1) (78774680500674391488001 / 62500000000000000000000) (377572255999 / 250000000000) (-122427744001 / 250000000000)
  have hratio : ((-122427744001 / 250000000000) / (377572255999 / 250000000000) : ℚ) = (-122427744001 / 377572255999) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV11_rounded_endpoints :
    (-250217470984753798914244951937301639623 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X4XV11Interval.1 ∧ manuscriptCase2X4XV11Interval.2 ≤ (-31277183873094222404134126089302762863 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-250217470984753798914244951937301639623 / 5000000000000000000000000000000000000000) : ℝ) ((-31277183873094222404134126089302762863 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-250217470984753798914244951937301639623 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV11Interval.2 : ℝ) ≤ ((-31277183873094222404134126089302762863 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV11_exact_interval.1, manuscriptCase2X4XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
