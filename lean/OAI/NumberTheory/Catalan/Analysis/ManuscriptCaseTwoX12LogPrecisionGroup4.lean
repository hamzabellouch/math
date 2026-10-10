import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX12

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X12XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (11554730802124581474649 / 10000000000000000000000) (60569925157 / 139430074843)

private theorem manuscriptCase2X12XV7_arg_eq : barrierCase2X12XV7LogArg = barrierComplex (1 / 1) (-39430074843 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV7LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV7Interval.1 : ℝ) (manuscriptCase2X12XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X12XV7LogArg).re ∈ _
  rw [manuscriptCase2X12XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X12XV7LogArg (0) (-1) (11554730802124581474649 / 10000000000000000000000) (139430074843 / 100000000000) (60569925157 / 100000000000)
  have hratio : ((60569925157 / 100000000000) / (139430074843 / 100000000000) : ℚ) = (60569925157 / 139430074843) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV7_rounded_endpoints :
    (453693251416149744365682969882795014049 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XV7Interval.1 ∧ manuscriptCase2X12XV7Interval.2 ≤ (56711656427018724892729391223206300361 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((453693251416149744365682969882795014049 / 10000000000000000000000000000000000000000) : ℝ) ((56711656427018724892729391223206300361 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((453693251416149744365682969882795014049 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV7Interval.2 : ℝ) ≤ ((56711656427018724892729391223206300361 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV7_exact_interval.1, manuscriptCase2X12XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (4700223881386504404650249 / 4000000000000000000000000) (1163206189443 / 2836793810557)

private theorem manuscriptCase2X12XV9_arg_eq : barrierCase2X12XV9LogArg = barrierComplex (1 / 1) (-836793810557 / 2000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV9LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV9Interval.1 : ℝ) (manuscriptCase2X12XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X12XV9LogArg).re ∈ _
  rw [manuscriptCase2X12XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X12XV9LogArg (0) (-1) (4700223881386504404650249 / 4000000000000000000000000) (2836793810557 / 2000000000000) (1163206189443 / 2000000000000)
  have hratio : ((1163206189443 / 2000000000000) / (2836793810557 / 2000000000000) : ℚ) = (1163206189443 / 2836793810557) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV9_rounded_endpoints :
    (-65753629359494955538639128837965693819 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X12XV9Interval.1 ∧ manuscriptCase2X12XV9Interval.2 ≤ (-32876814679747475070124885808883558081 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-65753629359494955538639128837965693819 / 2500000000000000000000000000000000000000) : ℝ) ((-32876814679747475070124885808883558081 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-65753629359494955538639128837965693819 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV9Interval.2 : ℝ) ≤ ((-32876814679747475070124885808883558081 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV9_exact_interval.1, manuscriptCase2X12XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (1852889164263491273209441 / 1562500000000000000000000) (711122310479 / 1788877689521)

private theorem manuscriptCase2X12XV11_arg_eq : barrierCase2X12XV11LogArg = barrierComplex (1 / 1) (-538877689521 / 1250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV11LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV11Interval.1 : ℝ) (manuscriptCase2X12XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X12XV11LogArg).re ∈ _
  rw [manuscriptCase2X12XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X12XV11LogArg (0) (-1) (1852889164263491273209441 / 1562500000000000000000000) (1788877689521 / 1250000000000) (711122310479 / 1250000000000)
  have hratio : ((711122310479 / 1250000000000) / (1788877689521 / 1250000000000) : ℚ) = (711122310479 / 1788877689521) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV11_rounded_endpoints :
    (450706007204584728986794693951149459147 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XV11Interval.1 ∧ manuscriptCase2X12XV11Interval.2 ≤ (450706007204584768349656604372554463219 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((450706007204584728986794693951149459147 / 10000000000000000000000000000000000000000) : ℝ) ((450706007204584768349656604372554463219 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((450706007204584728986794693951149459147 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV11Interval.2 : ℝ) ≤ ((450706007204584768349656604372554463219 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV11_exact_interval.1, manuscriptCase2X12XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
