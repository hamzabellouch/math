import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y0YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (23192638458207386881 / 19531250000000000000) (-41779611 / 250000000)

private theorem manuscriptCase2Y0YV7_arg_eq : barrierCase2Y0YV7LogArg = barrierComplex (19 / 100) (-793812609 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV7LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV7Interval.1 : ℝ) (manuscriptCase2Y0YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y0YV7LogArg).re ∈ _
  rw [manuscriptCase2Y0YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y0YV7LogArg (-5) (0) (23192638458207386881 / 19531250000000000000) (19 / 100) (-793812609 / 25000000000)
  have hratio : ((-793812609 / 25000000000) / (19 / 100) : ℚ) = (-41779611 / 250000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV7_rounded_endpoints :
    (-707704594451601085463927420713046683179 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV7Interval.1 ∧ manuscriptCase2Y0YV7Interval.2 ≤ (-2830818377806404341326633275502449165607 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-707704594451601085463927420713046683179 / 2500000000000000000000000000000000000000) : ℝ) ((-2830818377806404341326633275502449165607 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-707704594451601085463927420713046683179 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV7Interval.2 : ℝ) ≤ ((-2830818377806404341326633275502449165607 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV7_exact_interval.1, manuscriptCase2Y0YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y0YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (9047010803 / 20277989197)

private theorem manuscriptCase2Y0YV9_arg_eq : barrierCase2Y0YV9LogArg = barrierComplex (3519 / 40000) (-16846467591 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV9LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV9Interval.1 : ℝ) (manuscriptCase2Y0YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y0YV9LogArg).re ∈ _
  rw [manuscriptCase2Y0YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y0YV9LogArg (-7) (-1) (2218703626544613343281 / 1953125000000000000000) (60833967591 / 500000000000) (27141032409 / 500000000000)
  have hratio : ((27141032409 / 500000000000) / (60833967591 / 500000000000) : ℚ) = (9047010803 / 20277989197) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV9_rounded_endpoints :
    (-286375659669086566479106834334110343483 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV9Interval.1 ∧ manuscriptCase2Y0YV9Interval.2 ≤ (-572751319338173111126609246715064383411 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-286375659669086566479106834334110343483 / 5000000000000000000000000000000000000000) : ℝ) ((-572751319338173111126609246715064383411 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-286375659669086566479106834334110343483 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV9Interval.2 : ℝ) ≤ ((-572751319338173111126609246715064383411 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV9_exact_interval.1, manuscriptCase2Y0YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y0YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-9) (-1) (216102260916290816329 / 190734863281250000000) (-928772323 / 20768772323)

private theorem manuscriptCase2Y0YV11_arg_eq : barrierCase2Y0YV11LogArg = barrierComplex (496 / 15625) (-10848772323 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y0YV11LogArg, Case2PointData.Y0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y0YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y0YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y0YV11Interval.1 : ℝ) (manuscriptCase2Y0YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y0YV11LogArg).re ∈ _
  rw [manuscriptCase2Y0YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y0YV11LogArg (-9) (-1) (216102260916290816329 / 190734863281250000000) (20768772323 / 312500000000) (-928772323 / 312500000000)
  have hratio : ((-928772323 / 312500000000) / (20768772323 / 312500000000) : ℚ) = (-928772323 / 20768772323) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y0YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y0YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y0YV11_rounded_endpoints :
    (-117438382251365935589873722512720847631 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y0YV11Interval.1 ∧ manuscriptCase2Y0YV11Interval.2 ≤ (-117438382251365927704914913103570149767 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y0YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y0YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-117438382251365935589873722512720847631 / 2000000000000000000000000000000000000000) : ℝ) ((-117438382251365927704914913103570149767 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-117438382251365935589873722512720847631 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y0YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y0YV11Interval.2 : ℝ) ≤ ((-117438382251365927704914913103570149767 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y0YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y0YV11_exact_interval.1, manuscriptCase2Y0YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
