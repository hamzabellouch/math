import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY16

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y16YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-1) (0) (145161 / 80000) (0 / 1)

private theorem manuscriptCase2Y16YV3_arg_eq : barrierCase2Y16YV3LogArg = barrierComplex (381 / 400) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV3LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV3Interval.1 : ℝ) (manuscriptCase2Y16YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y16YV3LogArg).re ∈ _
  rw [manuscriptCase2Y16YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y16YV3LogArg (-1) (0) (145161 / 80000) (381 / 400) (0 / 1)
  have hratio : ((0 / 1) / (381 / 400) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV3_rounded_endpoints :
    (-24004748193071413478576891667353131017 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV3Interval.1 ∧ manuscriptCase2Y16YV3Interval.2 ≤ (-12002374096535706722548125460410383743 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-24004748193071413478576891667353131017 / 10000000000000000000000000000000000000000) : ℝ) ((-12002374096535706722548125460410383743 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-24004748193071413478576891667353131017 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV3Interval.2 : ℝ) ≤ ((-12002374096535706722548125460410383743 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV3_exact_interval.1, manuscriptCase2Y16YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y16YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-1) (0) (473027282 / 244140625) (0 / 1)

private theorem manuscriptCase2Y16YV4_arg_eq : barrierCase2Y16YV4LogArg = barrierComplex (15379 / 15625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV4LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV4Interval.1 : ℝ) (manuscriptCase2Y16YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y16YV4LogArg).re ∈ _
  rw [manuscriptCase2Y16YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y16YV4LogArg (-1) (0) (473027282 / 244140625) (15379 / 15625) (0 / 1)
  have hratio : ((0 / 1) / (15379 / 15625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV4_rounded_endpoints :
    (18437147473998438932834211754575697633 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV4Interval.1 ∧ manuscriptCase2Y16YV4Interval.2 ≤ (2304643434249804878353786923377483733 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((18437147473998438932834211754575697633 / 10000000000000000000000000000000000000000) : ℝ) ((2304643434249804878353786923377483733 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((18437147473998438932834211754575697633 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV4Interval.2 : ℝ) ≤ ((2304643434249804878353786923377483733 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV4_exact_interval.1, manuscriptCase2Y16YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y16YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (-1) (-1) (4760941 / 3125000) (-971 / 2929)

private theorem manuscriptCase2Y16YV5_arg_eq : barrierCase2Y16YV5LogArg = barrierComplex (979 / 2500) (-39 / 50) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV5LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV5Interval.1 : ℝ) (manuscriptCase2Y16YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y16YV5LogArg).re ∈ _
  rw [manuscriptCase2Y16YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y16YV5LogArg (-1) (-1) (4760941 / 3125000) (2929 / 2500) (-971 / 2500)
  have hratio : ((-971 / 2500) / (2929 / 2500) : ℚ) = (-971 / 2929) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV5_rounded_endpoints :
    (-1939911086339715529424417444829487505573 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV5Interval.1 ∧ manuscriptCase2Y16YV5Interval.2 ≤ (-1939911086339715459641376905590047784003 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-1939911086339715529424417444829487505573 / 10000000000000000000000000000000000000000) : ℝ) ((-1939911086339715459641376905590047784003 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1939911086339715529424417444829487505573 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV5Interval.2 : ℝ) ≤ ((-1939911086339715459641376905590047784003 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV5_exact_interval.1, manuscriptCase2Y16YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
