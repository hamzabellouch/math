import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX6

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X6XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2695709744934828828649 / 2500000000000000000000) (13989629907 / 50000000000)

private theorem manuscriptCase2X6XV7_arg_eq : barrierCase2X6XV7LogArg = barrierComplex (1 / 1) (13989629907 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV7LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV7Interval.1 : ℝ) (manuscriptCase2X6XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X6XV7LogArg).re ∈ _
  rw [manuscriptCase2X6XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X6XV7LogArg (0) (0) (2695709744934828828649 / 2500000000000000000000) (1 / 1) (13989629907 / 50000000000)
  have hratio : ((13989629907 / 50000000000) / (1 / 1) : ℚ) = (13989629907 / 50000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV7_rounded_endpoints :
    (-235427404388568413947435274872654450889 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X6XV7Interval.1 ∧ manuscriptCase2X6XV7Interval.2 ≤ (-235427404388568413947435274860560605481 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-235427404388568413947435274872654450889 / 5000000000000000000000000000000000000000) : ℝ) ((-235427404388568413947435274860560605481 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-235427404388568413947435274872654450889 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV7Interval.2 : ℝ) ≤ ((-235427404388568413947435274860560605481 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV7_exact_interval.1, manuscriptCase2X6XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1088144286481080129604249 / 1000000000000000000000000) (296891034693 / 1000000000000)

private theorem manuscriptCase2X6XV9_arg_eq : barrierCase2X6XV9LogArg = barrierComplex (1 / 1) (296891034693 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV9LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV9Interval.1 : ℝ) (manuscriptCase2X6XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X6XV9LogArg).re ∈ _
  rw [manuscriptCase2X6XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X6XV9LogArg (0) (0) (1088144286481080129604249 / 1000000000000000000000000) (1 / 1) (296891034693 / 1000000000000)
  have hratio : ((296891034693 / 1000000000000) / (1 / 1) : ℚ) = (296891034693 / 1000000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV9_rounded_endpoints :
    (157759358856601450034853033487693665807 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X6XV9Interval.1 ∧ manuscriptCase2X6XV9Interval.2 ≤ (31551871771320290006970606732457182199 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((157759358856601450034853033487693665807 / 10000000000000000000000000000000000000000) : ℝ) ((31551871771320290006970606732457182199 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((157759358856601450034853033487693665807 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV9Interval.2 : ℝ) ≤ ((31551871771320290006970606732457182199 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV9_exact_interval.1, manuscriptCase2X6XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X6XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (427179231248383028995441 / 390625000000000000000000) (191191608729 / 625000000000)

private theorem manuscriptCase2X6XV11_arg_eq : barrierCase2X6XV11LogArg = barrierComplex (1 / 1) (191191608729 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X6XV11LogArg, Case2PointData.X6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X6XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X6XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X6XV11Interval.1 : ℝ) (manuscriptCase2X6XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X6XV11LogArg).re ∈ _
  rw [manuscriptCase2X6XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X6XV11LogArg (0) (0) (427179231248383028995441 / 390625000000000000000000) (1 / 1) (191191608729 / 625000000000)
  have hratio : ((191191608729 / 625000000000) / (1 / 1) : ℚ) = (191191608729 / 625000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X6XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X6XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X6XV11_rounded_endpoints :
    (-15886974676894267729184658837326189847 / 500000000000000000000000000000000000000) ≤ manuscriptCase2X6XV11Interval.1 ∧ manuscriptCase2X6XV11Interval.2 ≤ (-158869746768942677291846587684018781523 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X6XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X6XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X6 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-15886974676894267729184658837326189847 / 500000000000000000000000000000000000000) : ℝ) ((-158869746768942677291846587684018781523 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-15886974676894267729184658837326189847 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X6XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X6XV11Interval.2 : ℝ) ≤ ((-158869746768942677291846587684018781523 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X6XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X6XV11_exact_interval.1, manuscriptCase2X6XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
