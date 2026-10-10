import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX18

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X18XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (181 / 100) (-1 / 19)

private theorem manuscriptCase2X18XV7_arg_eq : barrierCase2X18XV7LogArg = barrierComplex (1 / 1) (9 / 10) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV7LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV7Interval.1 : ℝ) (manuscriptCase2X18XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X18XV7LogArg).re ∈ _
  rw [manuscriptCase2X18XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X18XV7LogArg (0) (1) (181 / 100) (19 / 10) (-1 / 10)
  have hratio : ((-1 / 10) / (19 / 10) : ℚ) = (-1 / 19) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV7_rounded_endpoints :
    (-49094611771958286941281657332686048841 / 312500000000000000000000000000000000000) ≤ manuscriptCase2X18XV7Interval.1 ∧ manuscriptCase2X18XV7Interval.2 ≤ (-1571027576702665127400072461364232463057 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-49094611771958286941281657332686048841 / 312500000000000000000000000000000000000) : ℝ) ((-1571027576702665127400072461364232463057 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-49094611771958286941281657332686048841 / 312500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV7Interval.2 : ℝ) ≤ ((-1571027576702665127400072461364232463057 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV7_exact_interval.1, manuscriptCase2X18XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (76481 / 40000) (-9 / 391)

private theorem manuscriptCase2X18XV9_arg_eq : barrierCase2X18XV9LogArg = barrierComplex (1 / 1) (191 / 200) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV9LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV9Interval.1 : ℝ) (manuscriptCase2X18XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X18XV9LogArg).re ∈ _
  rw [manuscriptCase2X18XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X18XV9LogArg (0) (1) (76481 / 40000) (391 / 200) (-9 / 200)
  have hratio : ((-9 / 200) / (391 / 200) : ℚ) = (-9 / 391) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV9_rounded_endpoints :
    (43202893470376993121061029858617884273 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X18XV9Interval.1 ∧ manuscriptCase2X18XV9Interval.2 ≤ (345623147763015966562967023192991090773 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((43202893470376993121061029858617884273 / 1250000000000000000000000000000000000000) : ℝ) ((345623147763015966562967023192991090773 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((43202893470376993121061029858617884273 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV9Interval.2 : ℝ) ≤ ((345623147763015966562967023192991090773 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV9_exact_interval.1, manuscriptCase2X18XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (1) (30754 / 15625) (-1 / 124)

private theorem manuscriptCase2X18XV11_arg_eq : barrierCase2X18XV11LogArg = barrierComplex (1 / 1) (123 / 125) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV11LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV11Interval.1 : ℝ) (manuscriptCase2X18XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X18XV11LogArg).re ∈ _
  rw [manuscriptCase2X18XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X18XV11LogArg (0) (1) (30754 / 15625) (248 / 125) (-2 / 125)
  have hratio : ((-2 / 125) / (248 / 125) : ℚ) = (-1 / 124) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV11_rounded_endpoints :
    (-809231117446464923078518529037973771311 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X18XV11Interval.1 ∧ manuscriptCase2X18XV11Interval.2 ≤ (-202307779361616220928268288699889626359 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-809231117446464923078518529037973771311 / 10000000000000000000000000000000000000000) : ℝ) ((-202307779361616220928268288699889626359 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-809231117446464923078518529037973771311 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV11Interval.2 : ℝ) ≤ ((-202307779361616220928268288699889626359 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV11_exact_interval.1, manuscriptCase2X18XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
