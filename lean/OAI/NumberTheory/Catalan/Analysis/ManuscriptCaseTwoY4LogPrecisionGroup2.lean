import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY4

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y4YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (116121632550302254081 / 78125000000000000000) (4750000000 / 9672596991)

private theorem manuscriptCase2Y4YV7_arg_eq : barrierCase2Y4YV7LogArg = barrierComplex (19 / 100) (-9672596991 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV7LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV7Interval.1 : ℝ) (manuscriptCase2Y4YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y4YV7LogArg).re ∈ _
  rw [manuscriptCase2Y4YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y4YV7LogArg (-3) (-2) (116121632550302254081 / 78125000000000000000) (9672596991 / 12500000000) (19 / 50)
  have hratio : ((19 / 50) / (9672596991 / 12500000000) : ℚ) = (4750000000 / 9672596991) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV7_rounded_endpoints :
    (-1500375455617389538482959811532899792469 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV7Interval.1 ∧ manuscriptCase2Y4YV7Interval.2 ≤ (-3000750911234778944561366086269304313709 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-1500375455617389538482959811532899792469 / 5000000000000000000000000000000000000000) : ℝ) ((-3000750911234778944561366086269304313709 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1500375455617389538482959811532899792469 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV7Interval.2 : ℝ) ≤ ((-3000750911234778944561366086269304313709 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV7_exact_interval.1, manuscriptCase2Y4YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y4YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (14662500000 / 68424667603)

private theorem manuscriptCase2Y4YV9_arg_eq : barrierCase2Y4YV9LogArg = barrierComplex (3519 / 40000) (-205274002809 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV9LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV9Interval.1 : ℝ) (manuscriptCase2Y4YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y4YV9LogArg).re ∈ _
  rw [manuscriptCase2Y4YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y4YV9LogArg (-3) (-2) (44072316385479339890481 / 31250000000000000000000) (205274002809 / 250000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (205274002809 / 250000000000) : ℚ) = (14662500000 / 68424667603) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV9_rounded_endpoints :
    (519418125007177427676472175021484156041 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV9Interval.1 ∧ manuscriptCase2Y4YV9Interval.2 ≤ (6492726562589718386609844361840167647 / 125000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((519418125007177427676472175021484156041 / 10000000000000000000000000000000000000000) : ℝ) ((6492726562589718386609844361840167647 / 125000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((519418125007177427676472175021484156041 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV9Interval.2 : ℝ) ≤ ((6492726562589718386609844361840167647 / 125000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV9_exact_interval.1, manuscriptCase2Y4YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y4YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (9920000000 / 132192158877)

private theorem manuscriptCase2Y4YV11_arg_eq : barrierCase2Y4YV11LogArg = barrierComplex (496 / 15625) (-132192158877 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV11LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV11Interval.1 : ℝ) (manuscriptCase2Y4YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y4YV11LogArg).re ∈ _
  rw [manuscriptCase2Y4YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y4YV11LogArg (-3) (-2) (17573173268562009901129 / 12207031250000000000000) (132192158877 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (132192158877 / 156250000000) : ℚ) = (9920000000 / 132192158877) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV11_rounded_endpoints :
    (-1536109516117992530287931957044075802119 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV11Interval.1 ∧ manuscriptCase2Y4YV11Interval.2 ≤ (-307221903223598490308485500761813468477 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-1536109516117992530287931957044075802119 / 10000000000000000000000000000000000000000) : ℝ) ((-307221903223598490308485500761813468477 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1536109516117992530287931957044075802119 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV11Interval.2 : ℝ) ≤ ((-307221903223598490308485500761813468477 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV11_exact_interval.1, manuscriptCase2Y4YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
