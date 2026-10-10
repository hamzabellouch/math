import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY17

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y17YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (9293 / 5000) (19 / 135)

private theorem manuscriptCase2Y17YV7_arg_eq : barrierCase2Y17YV7LogArg = barrierComplex (19 / 100) (-27 / 20) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV7LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV7Interval.1 : ℝ) (manuscriptCase2Y17YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y17YV7LogArg).re ∈ _
  rw [manuscriptCase2Y17YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y17YV7LogArg (0) (-2) (9293 / 5000) (27 / 10) (19 / 50)
  have hratio : ((19 / 50) / (27 / 10) : ℚ) = (19 / 135) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV7_rounded_endpoints :
    (-1674319807384064670987340042207583193293 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV7Interval.1 ∧ manuscriptCase2Y17YV7Interval.2 ≤ (-837159903692032280772108874364758576471 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-1674319807384064670987340042207583193293 / 10000000000000000000000000000000000000000) : ℝ) ((-837159903692032280772108874364758576471 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1674319807384064670987340042207583193293 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV7Interval.2 : ℝ) ≤ ((-837159903692032280772108874364758576471 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV7_exact_interval.1, manuscriptCase2Y17YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y17YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3295673361 / 3200000000) (1173 / 19100)

private theorem manuscriptCase2Y17YV9_arg_eq : barrierCase2Y17YV9LogArg = barrierComplex (3519 / 40000) (-573 / 400) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV9LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV9Interval.1 : ℝ) (manuscriptCase2Y17YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y17YV9LogArg).re ∈ _
  rw [manuscriptCase2Y17YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y17YV9LogArg (1) (-2) (3295673361 / 3200000000) (573 / 200) (3519 / 20000)
  have hratio : ((3519 / 20000) / (573 / 200) : ℚ) = (1173 / 19100) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV9_rounded_endpoints :
    (1019973384023334606900064324943422976847 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV9Interval.1 ∧ manuscriptCase2Y17YV9Interval.2 ≤ (1019973384023334650107181579316805014303 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((1019973384023334606900064324943422976847 / 10000000000000000000000000000000000000000) : ℝ) ((1019973384023334650107181579316805014303 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1019973384023334606900064324943422976847 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV9Interval.2 : ℝ) ≤ ((1019973384023334650107181579316805014303 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV9_exact_interval.1, manuscriptCase2Y17YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y17YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (2128499689 / 1953125000) (992 / 46125)

private theorem manuscriptCase2Y17YV11_arg_eq : barrierCase2Y17YV11LogArg = barrierComplex (496 / 15625) (-369 / 250) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV11LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV11Interval.1 : ℝ) (manuscriptCase2Y17YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y17YV11LogArg).re ∈ _
  rw [manuscriptCase2Y17YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y17YV11LogArg (1) (-2) (2128499689 / 1953125000) (369 / 125) (992 / 15625)
  have hratio : ((992 / 15625) / (369 / 125) : ℚ) = (992 / 46125) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV11_rounded_endpoints :
    (-430560662464474113428883758946349893001 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV11Interval.1 ∧ manuscriptCase2Y17YV11Interval.2 ≤ (-344448529971579274996781680266440108561 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-430560662464474113428883758946349893001 / 2500000000000000000000000000000000000000) : ℝ) ((-344448529971579274996781680266440108561 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-430560662464474113428883758946349893001 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV11Interval.2 : ℝ) ≤ ((-344448529971579274996781680266440108561 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV11_exact_interval.1, manuscriptCase2Y17YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
