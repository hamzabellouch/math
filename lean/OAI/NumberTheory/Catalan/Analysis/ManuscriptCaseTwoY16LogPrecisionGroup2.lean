import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY16

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y16YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-1) (-2) (8461 / 5000) (19 / 90)

private theorem manuscriptCase2Y16YV7_arg_eq : barrierCase2Y16YV7LogArg = barrierComplex (19 / 100) (-9 / 10) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV7LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV7Interval.1 : ℝ) (manuscriptCase2Y16YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y16YV7LogArg).re ∈ _
  rw [manuscriptCase2Y16YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y16YV7LogArg (-1) (-2) (8461 / 5000) (9 / 5) (19 / 50)
  have hratio : ((19 / 50) / (9 / 5) : ℚ) = (19 / 90) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV7_rounded_endpoints :
    (-218791486338259720848722833563540833171 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV7Interval.1 ∧ manuscriptCase2Y16YV7Interval.2 ≤ (-2187914863382597098940474416835779795471 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-218791486338259720848722833563540833171 / 1000000000000000000000000000000000000000) : ℝ) ((-2187914863382597098940474416835779795471 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-218791486338259720848722833563540833171 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV7Interval.2 : ℝ) ≤ ((-2187914863382597098940474416835779795471 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV7_exact_interval.1, manuscriptCase2Y16YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y16YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-1) (-2) (1471623361 / 800000000) (3519 / 38200)

private theorem manuscriptCase2Y16YV9_arg_eq : barrierCase2Y16YV9LogArg = barrierComplex (3519 / 40000) (-191 / 200) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV9LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV9Interval.1 : ℝ) (manuscriptCase2Y16YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y16YV9LogArg).re ∈ _
  rw [manuscriptCase2Y16YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y16YV9LogArg (-1) (-2) (1471623361 / 800000000) (191 / 100) (3519 / 20000)
  have hratio : ((3519 / 20000) / (191 / 100) : ℚ) = (3519 / 38200) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV9_rounded_endpoints :
    (173375358277033478611165990323321530171 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV9Interval.1 ∧ manuscriptCase2Y16YV9Interval.2 ≤ (866876791385167436263207437913195591647 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((173375358277033478611165990323321530171 / 2000000000000000000000000000000000000000) : ℝ) ((866876791385167436263207437913195591647 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((173375358277033478611165990323321530171 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV9Interval.2 : ℝ) ≤ ((866876791385167436263207437913195591647 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV9_exact_interval.1, manuscriptCase2Y16YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y16YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-1) (-2) (473273282 / 244140625) (496 / 15375)

private theorem manuscriptCase2Y16YV11_arg_eq : barrierCase2Y16YV11LogArg = barrierComplex (496 / 15625) (-123 / 125) := by
  apply Complex.ext <;> norm_num [barrierCase2Y16YV11LogArg, Case2PointData.Y16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y16YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y16YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y16YV11Interval.1 : ℝ) (manuscriptCase2Y16YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y16YV11LogArg).re ∈ _
  rw [manuscriptCase2Y16YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y16YV11LogArg (-1) (-2) (473273282 / 244140625) (246 / 125) (992 / 15625)
  have hratio : ((992 / 15625) / (246 / 125) : ℚ) = (496 / 15375) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y16YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y16YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y16YV11_rounded_endpoints :
    (-417234768444298696588453805137304780457 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y16YV11Interval.1 ∧ manuscriptCase2Y16YV11Interval.2 ≤ (-1668939073777194707620775758823560347063 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y16YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y16YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y16 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-417234768444298696588453805137304780457 / 2500000000000000000000000000000000000000) : ℝ) ((-1668939073777194707620775758823560347063 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-417234768444298696588453805137304780457 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y16YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y16YV11Interval.2 : ℝ) ≤ ((-1668939073777194707620775758823560347063 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y16YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y16YV11_exact_interval.1, manuscriptCase2Y16YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
