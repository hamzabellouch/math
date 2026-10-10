import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X0XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (1091667815413534509889 / 625000000000000000000) (-3397504417 / 46602495583)

private theorem manuscriptCase2X0XV7_arg_eq : barrierCase2X0XV7LogArg = barrierComplex (1 / 1) (21602495583 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV7LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV7Interval.1 : ℝ) (manuscriptCase2X0XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X0XV7LogArg).re ∈ _
  rw [manuscriptCase2X0XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X0XV7LogArg (0) (1) (1091667815413534509889 / 625000000000000000000) (46602495583 / 25000000000) (-3397504417 / 25000000000)
  have hratio : ((-3397504417 / 25000000000) / (46602495583 / 25000000000) : ℚ) = (-3397504417 / 46602495583) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV7_rounded_endpoints :
    (-75632113185680454936521727101 / 500000000000000000000000000000) ≤ manuscriptCase2X0XV7Interval.1 ∧ manuscriptCase2X0XV7Interval.2 ≤ (-7563211318568045220049574473 / 50000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-75632113185680454936521727101 / 500000000000000000000000000000) : ℝ) ((-7563211318568045220049574473 / 50000000000000000000000000000) : ℝ) := by
  have hlo : ((-75632113185680454936521727101 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV7Interval.2 : ℝ) ≤ ((-7563211318568045220049574473 / 50000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV7_exact_interval.1, manuscriptCase2X0XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (460179118198779659941489 / 250000000000000000000000) (-41547038183 / 958452961817)

private theorem manuscriptCase2X0XV9_arg_eq : barrierCase2X0XV9LogArg = barrierComplex (1 / 1) (458452961817 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV9LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV9Interval.1 : ℝ) (manuscriptCase2X0XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X0XV9LogArg).re ∈ _
  rw [manuscriptCase2X0XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X0XV9LogArg (0) (1) (460179118198779659941489 / 250000000000000000000000) (958452961817 / 500000000000) (-41547038183 / 500000000000)
  have hratio : ((-41547038183 / 500000000000) / (958452961817 / 500000000000) : ℚ) = (-41547038183 / 958452961817) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV9_rounded_endpoints :
    (2124301308092072155819768613 / 62500000000000000000000000000) ≤ manuscriptCase2X0XV9Interval.1 ∧ manuscriptCase2X0XV9Interval.2 ≤ (33988820929473156652369211959 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((2124301308092072155819768613 / 62500000000000000000000000000) : ℝ) ((33988820929473156652369211959 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((2124301308092072155819768613 / 62500000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV9Interval.2 : ℝ) ≤ ((33988820929473156652369211959 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV9_exact_interval.1, manuscriptCase2X0XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (1) (184819427523350167902601 / 97656250000000000000000) (-17265893699 / 607734106301)

private theorem manuscriptCase2X0XV11_arg_eq : barrierCase2X0XV11LogArg = barrierComplex (1 / 1) (295234106301 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV11LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV11Interval.1 : ℝ) (manuscriptCase2X0XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X0XV11LogArg).re ∈ _
  rw [manuscriptCase2X0XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X0XV11LogArg (0) (1) (184819427523350167902601 / 97656250000000000000000) (607734106301 / 312500000000) (-17265893699 / 312500000000)
  have hratio : ((-17265893699 / 312500000000) / (607734106301 / 312500000000) : ℚ) = (-17265893699 / 607734106301) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV11_rounded_endpoints :
    (-15783264051777411528829951433 / 200000000000000000000000000000) ≤ manuscriptCase2X0XV11Interval.1 ∧ manuscriptCase2X0XV11Interval.2 ≤ (-15783264051777410741575237479 / 200000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-15783264051777411528829951433 / 200000000000000000000000000000) : ℝ) ((-15783264051777410741575237479 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-15783264051777411528829951433 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV11Interval.2 : ℝ) ≤ ((-15783264051777410741575237479 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV11_exact_interval.1, manuscriptCase2X0XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
