import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX15

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X15XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (3925534286370865359481 / 2500000000000000000000) (12243751691 / 87756248309)

private theorem manuscriptCase2X15XV7_arg_eq : barrierCase2X15XV7LogArg = barrierComplex (1 / 1) (-37756248309 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV7LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV7Interval.1 : ℝ) (manuscriptCase2X15XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X15XV7LogArg).re ∈ _
  rw [manuscriptCase2X15XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X15XV7LogArg (0) (-1) (3925534286370865359481 / 2500000000000000000000) (87756248309 / 50000000000) (12243751691 / 50000000000)
  have hratio : ((12243751691 / 50000000000) / (87756248309 / 50000000000) : ℚ) = (12243751691 / 87756248309) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV7_rounded_endpoints :
    (77841000382758682627787407883447387319 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X15XV7Interval.1 ∧ manuscriptCase2X15XV7Interval.2 ≤ (622728003062069515742765220494540002123 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((77841000382758682627787407883447387319 / 1250000000000000000000000000000000000000) : ℝ) ((622728003062069515742765220494540002123 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((77841000382758682627787407883447387319 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV7Interval.2 : ℝ) ≤ ((622728003062069515742765220494540002123 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV7_exact_interval.1, manuscriptCase2X15XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (1642036003717228878755881 / 1000000000000000000000000) (198728508109 / 1801271491891)

private theorem manuscriptCase2X15XV9_arg_eq : barrierCase2X15XV9LogArg = barrierComplex (1 / 1) (-801271491891 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV9LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV9Interval.1 : ℝ) (manuscriptCase2X15XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X15XV9LogArg).re ∈ _
  rw [manuscriptCase2X15XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X15XV9LogArg (0) (-1) (1642036003717228878755881 / 1000000000000000000000000) (1801271491891 / 1000000000000) (198728508109 / 1000000000000)
  have hratio : ((198728508109 / 1000000000000) / (1801271491891 / 1000000000000) : ℚ) = (198728508109 / 1801271491891) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV9_rounded_endpoints :
    (-121333783643869237074879422632157711387 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X15XV9Interval.1 ∧ manuscriptCase2X15XV9Interval.2 ≤ (-242667567287738463353629207532313084427 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-121333783643869237074879422632157711387 / 2500000000000000000000000000000000000000) : ℝ) ((-242667567287738463353629207532313084427 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-121333783643869237074879422632157711387 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV9Interval.2 : ℝ) ≤ ((-242667567287738463353629207532313084427 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV9_exact_interval.1, manuscriptCase2X15XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (656883126154380518809729 / 390625000000000000000000) (108997939777 / 1141002060223)

private theorem manuscriptCase2X15XV11_arg_eq : barrierCase2X15XV11LogArg = barrierComplex (1 / 1) (-516002060223 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XV11LogArg, Case2PointData.X15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XV11Interval.1 : ℝ) (manuscriptCase2X15XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X15XV11LogArg).re ∈ _
  rw [manuscriptCase2X15XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X15XV11LogArg (0) (-1) (656883126154380518809729 / 390625000000000000000000) (1141002060223 / 625000000000) (108997939777 / 625000000000)
  have hratio : ((108997939777 / 625000000000) / (1141002060223 / 625000000000) : ℚ) = (108997939777 / 1141002060223) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XV11_rounded_endpoints :
    (776074673323072950240080181773673588397 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XV11Interval.1 ∧ manuscriptCase2X15XV11Interval.2 ≤ (776074673323072989602424334716787503281 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X15 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((776074673323072950240080181773673588397 / 10000000000000000000000000000000000000000) : ℝ) ((776074673323072989602424334716787503281 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((776074673323072950240080181773673588397 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XV11Interval.2 : ℝ) ≤ ((776074673323072989602424334716787503281 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XV11_exact_interval.1, manuscriptCase2X15XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
