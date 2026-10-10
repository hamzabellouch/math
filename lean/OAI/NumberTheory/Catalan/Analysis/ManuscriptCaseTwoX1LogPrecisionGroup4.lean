import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX1

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X1XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1029823033014906124369 / 625000000000000000000) (-4879785463 / 45120214537)

private theorem manuscriptCase2X1XV7_arg_eq : barrierCase2X1XV7LogArg = barrierComplex (1 / 1) (20120214537 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV7LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV7Interval.1 : ℝ) (manuscriptCase2X1XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X1XV7LogArg).re ∈ _
  rw [manuscriptCase2X1XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X1XV7LogArg (0) (1) (1029823033014906124369 / 625000000000000000000) (45120214537 / 25000000000) (-4879785463 / 25000000000)
  have hratio : ((-4879785463 / 25000000000) / (45120214537 / 25000000000) : ℚ) = (-4879785463 / 45120214537) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV7_rounded_endpoints :
    (-141418196714875241235803156859650174651 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X1XV7Interval.1 ∧ manuscriptCase2X1XV7Interval.2 ≤ (-1414181967148752357637564571283111677091 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-141418196714875241235803156859650174651 / 1000000000000000000000000000000000000000) : ℝ) ((-1414181967148752357637564571283111677091 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-141418196714875241235803156859650174651 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV7Interval.2 : ℝ) ≤ ((-1414181967148752357637564571283111677091 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV7_exact_interval.1, manuscriptCase2X1XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (432325297128602349667969 / 250000000000000000000000) (-73004335937 / 926995664063)

private theorem manuscriptCase2X1XV9_arg_eq : barrierCase2X1XV9LogArg = barrierComplex (1 / 1) (426995664063 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV9LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV9Interval.1 : ℝ) (manuscriptCase2X1XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X1XV9LogArg).re ∈ _
  rw [manuscriptCase2X1XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X1XV9LogArg (0) (1) (432325297128602349667969 / 250000000000000000000000) (926995664063 / 500000000000) (-73004335937 / 500000000000)
  have hratio : ((-73004335937 / 500000000000) / (926995664063 / 500000000000) : ℚ) = (-73004335937 / 926995664063) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV9_rounded_endpoints :
    (164664399685707495048724291703858833839 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X1XV9Interval.1 ∧ manuscriptCase2X1XV9Interval.2 ≤ (329328799371415011689713737579567687239 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((164664399685707495048724291703858833839 / 5000000000000000000000000000000000000000) : ℝ) ((329328799371415011689713737579567687239 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((164664399685707495048724291703858833839 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV9Interval.2 : ℝ) ≤ ((329328799371415011689713737579567687239 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV9_exact_interval.1, manuscriptCase2X1XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (1) (173268196499784132784921 / 97656250000000000000000) (-37523734661 / 587476265339)

private theorem manuscriptCase2X1XV11_arg_eq : barrierCase2X1XV11LogArg = barrierComplex (1 / 1) (274976265339 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV11LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV11Interval.1 : ℝ) (manuscriptCase2X1XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X1XV11LogArg).re ∈ _
  rw [manuscriptCase2X1XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X1XV11LogArg (0) (1) (173268196499784132784921 / 97656250000000000000000) (587476265339 / 312500000000) (-37523734661 / 312500000000)
  have hratio : ((-37523734661 / 312500000000) / (587476265339 / 312500000000) : ℚ) = (-37523734661 / 587476265339) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV11_rounded_endpoints :
    (-150812020056340084935691653763788714643 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X1XV11Interval.1 ∧ manuscriptCase2X1XV11Interval.2 ≤ (-30162404011268015412644201826465186563 / 400000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-150812020056340084935691653763788714643 / 2000000000000000000000000000000000000000) : ℝ) ((-30162404011268015412644201826465186563 / 400000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-150812020056340084935691653763788714643 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV11Interval.2 : ℝ) ≤ ((-30162404011268015412644201826465186563 / 400000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV11_exact_interval.1, manuscriptCase2X1XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
