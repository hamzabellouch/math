import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX2

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X2XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (1) (0) (118720082383255370578729 / 80000000000000000000000) (0 / 1)

private theorem manuscriptCase2X2XV3_arg_eq : barrierCase2X2XV3LogArg = barrierComplex (344557807027 / 200000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV3LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV3Interval.1 : ℝ) (manuscriptCase2X2XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X2XV3LogArg).re ∈ _
  rw [manuscriptCase2X2XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X2XV3LogArg (1) (0) (118720082383255370578729 / 80000000000000000000000) (344557807027 / 200000000000) (0 / 1)
  have hratio : ((0 / 1) / (344557807027 / 200000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV3_rounded_endpoints :
    (-26830791822499711791114284536309665171 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV3Interval.1 ∧ manuscriptCase2X2XV3Interval.2 ≤ (-268307918224997117877835251009661620537 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-26830791822499711791114284536309665171 / 1000000000000000000000000000000000000000) : ℝ) ((-268307918224997117877835251009661620537 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-26830791822499711791114284536309665171 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV3Interval.2 : ℝ) ≤ ((-268307918224997117877835251009661620537 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV3_exact_interval.1, manuscriptCase2X2XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (0 / 1)

private theorem manuscriptCase2X2XV4_arg_eq : barrierCase2X2XV4LogArg = barrierComplex (2185821592859 / 1250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV4LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV4Interval.1 : ℝ) (manuscriptCase2X2XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X2XV4LogArg).re ∈ _
  rw [manuscriptCase2X2XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X2XV4LogArg (1) (0) (4777816035808655959793881 / 3125000000000000000000000) (2185821592859 / 1250000000000) (0 / 1)
  have hratio : ((0 / 1) / (2185821592859 / 1250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV4_rounded_endpoints :
    (64927863776713681904827105810040851289 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV4Interval.1 ∧ manuscriptCase2X2XV4Interval.2 ≤ (649278637767136819126722626022225162903 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((64927863776713681904827105810040851289 / 1000000000000000000000000000000000000000) : ℝ) ((649278637767136819126722626022225162903 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((64927863776713681904827105810040851289 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV4Interval.2 : ℝ) ≤ ((649278637767136819126722626022225162903 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV4_exact_interval.1, manuscriptCase2X2XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (1) (338045084514417226177969 / 250000000000000000000000) (-203276080313 / 796723919687)

private theorem manuscriptCase2X2XV5_arg_eq : barrierCase2X2XV5LogArg = barrierComplex (1 / 1) (296723919687 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV5LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV5Interval.1 : ℝ) (manuscriptCase2X2XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X2XV5LogArg).re ∈ _
  rw [manuscriptCase2X2XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X2XV5LogArg (0) (1) (338045084514417226177969 / 250000000000000000000000) (796723919687 / 500000000000) (-203276080313 / 500000000000)
  have hratio : ((-203276080313 / 500000000000) / (796723919687 / 500000000000) : ℚ) = (-203276080313 / 796723919687) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV5_rounded_endpoints :
    (-824151784598508959315886495523703077877 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV5Interval.1 ∧ manuscriptCase2X2XV5Interval.2 ≤ (-82415178459850888962481074542957233907 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-824151784598508959315886495523703077877 / 10000000000000000000000000000000000000000) : ℝ) ((-82415178459850888962481074542957233907 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-824151784598508959315886495523703077877 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV5Interval.2 : ℝ) ≤ ((-82415178459850888962481074542957233907 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV5_exact_interval.1, manuscriptCase2X2XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
