import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY6

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y6YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-1) (-2) (25059280084989009289 / 19531250000000000000) (1187500000 / 4863036483)

private theorem manuscriptCase2Y6YV7_arg_eq : barrierCase2Y6YV7LogArg = barrierComplex (19 / 100) (-4863036483 / 6250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV7LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV7Interval.1 : ℝ) (manuscriptCase2Y6YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y6YV7LogArg).re ∈ _
  rw [manuscriptCase2Y6YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y6YV7LogArg (-1) (-2) (25059280084989009289 / 19531250000000000000) (4863036483 / 3125000000) (19 / 50)
  have hratio : ((19 / 50) / (4863036483 / 3125000000) : ℚ) = (1187500000 / 4863036483) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV7_rounded_endpoints :
    (-2357330237465567007166542725257150951949 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV7Interval.1 ∧ manuscriptCase2Y6YV7Interval.2 ≤ (-2357330237465566897619795585735249510609 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-2357330237465567007166542725257150951949 / 10000000000000000000000000000000000000000) : ℝ) ((-2357330237465566897619795585735249510609 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2357330237465567007166542725257150951949 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV7Interval.2 : ℝ) ≤ ((-2357330237465566897619795585735249510609 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV7_exact_interval.1, manuscriptCase2Y6YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y6YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-1) (-2) (10772087884756168800889 / 7812500000000000000000) (10996875000 / 103204440917)

private theorem manuscriptCase2Y6YV9_arg_eq : barrierCase2Y6YV9LogArg = barrierComplex (3519 / 40000) (-103204440917 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV9LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV9Interval.1 : ℝ) (manuscriptCase2Y6YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y6YV9LogArg).re ∈ _
  rw [manuscriptCase2Y6YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y6YV9LogArg (-1) (-2) (10772087884756168800889 / 7812500000000000000000) (103204440917 / 62500000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (103204440917 / 62500000000) : ℚ) = (10996875000 / 103204440917) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV9_rounded_endpoints :
    (3240496796428190161089933566184712453 / 40000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV9Interval.1 ∧ manuscriptCase2Y6YV9Interval.2 ≤ (405062099553523791739800322959793989211 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((3240496796428190161089933566184712453 / 40000000000000000000000000000000000000) : ℝ) ((405062099553523791739800322959793989211 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((3240496796428190161089933566184712453 / 40000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV9Interval.2 : ℝ) ≤ ((405062099553523791739800322959793989211 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV9_exact_interval.1, manuscriptCase2Y6YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y6YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-1) (-2) (4423281196290724957201 / 3051757812500000000000) (2480000000 / 66461498601)

private theorem manuscriptCase2Y6YV11_arg_eq : barrierCase2Y6YV11LogArg = barrierComplex (496 / 15625) (-66461498601 / 78125000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV11LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV11Interval.1 : ℝ) (manuscriptCase2Y6YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y6YV11LogArg).re ∈ _
  rw [manuscriptCase2Y6YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y6YV11LogArg (-1) (-2) (4423281196290724957201 / 3051757812500000000000) (66461498601 / 39062500000) (992 / 15625)
  have hratio : ((992 / 15625) / (66461498601 / 39062500000) : ℚ) = (2480000000 / 66461498601) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV11_rounded_endpoints :
    (-412129453291083685731586532693393616047 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV11Interval.1 ∧ manuscriptCase2Y6YV11Interval.2 ≤ (-1648517813164334664194719496318748694391 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-412129453291083685731586532693393616047 / 2500000000000000000000000000000000000000) : ℝ) ((-1648517813164334664194719496318748694391 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-412129453291083685731586532693393616047 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV11Interval.2 : ℝ) ≤ ((-1648517813164334664194719496318748694391 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV11_exact_interval.1, manuscriptCase2Y6YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
