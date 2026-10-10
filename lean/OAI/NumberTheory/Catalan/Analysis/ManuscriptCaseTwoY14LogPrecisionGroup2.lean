import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY14

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y14YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (511084712089128183481 / 312500000000000000000) (2375000000 / 22482083691)

private theorem manuscriptCase2Y14YV7_arg_eq : barrierCase2Y14YV7LogArg = barrierComplex (19 / 100) (-22482083691 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV7LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV7Interval.1 : ℝ) (manuscriptCase2Y14YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y14YV7LogArg).re ∈ _
  rw [manuscriptCase2Y14YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y14YV7LogArg (1) (-2) (511084712089128183481 / 312500000000000000000) (22482083691 / 6250000000) (19 / 50)
  have hratio : ((19 / 50) / (22482083691 / 6250000000) : ℚ) = (2375000000 / 22482083691) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV7_rounded_endpoints :
    (-1283613477061238312189019604020924727051 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV7Interval.1 ∧ manuscriptCase2Y14YV7Interval.2 ≤ (-641806738530619101321135919890004474847 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-1283613477061238312189019604020924727051 / 10000000000000000000000000000000000000000) : ℝ) ((-641806738530619101321135919890004474847 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1283613477061238312189019604020924727051 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV7Interval.2 : ℝ) ≤ ((-641806738530619101321135919890004474847 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV7_exact_interval.1, manuscriptCase2Y14YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y14YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (228127005793364787179881 / 125000000000000000000000) (21993750000 / 477119776109)

private theorem manuscriptCase2Y14YV9_arg_eq : barrierCase2Y14YV9LogArg = barrierComplex (3519 / 40000) (-477119776109 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV9LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV9Interval.1 : ℝ) (manuscriptCase2Y14YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y14YV9LogArg).re ∈ _
  rw [manuscriptCase2Y14YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y14YV9LogArg (1) (-2) (228127005793364787179881 / 125000000000000000000000) (477119776109 / 125000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (477119776109 / 125000000000) : ℚ) = (21993750000 / 477119776109) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV9_rounded_endpoints :
    (1124808993742340191678553179907157917489 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV9Interval.1 ∧ manuscriptCase2Y14YV9Interval.2 ≤ (224961798748468046977167010209261872427 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((1124808993742340191678553179907157917489 / 10000000000000000000000000000000000000000) : ℝ) ((224961798748468046977167010209261872427 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1124808993742340191678553179907157917489 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV9Interval.2 : ℝ) ≤ ((224961798748468046977167010209261872427 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV9_exact_interval.1, manuscriptCase2Y14YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y14YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (94430324977424941825729 / 48828125000000000000000) (4960000000 / 307255143777)

private theorem manuscriptCase2Y14YV11_arg_eq : barrierCase2Y14YV11LogArg = barrierComplex (496 / 15625) (-307255143777 / 156250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV11LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV11Interval.1 : ℝ) (manuscriptCase2Y14YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y14YV11LogArg).re ∈ _
  rw [manuscriptCase2Y14YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y14YV11LogArg (1) (-2) (94430324977424941825729 / 48828125000000000000000) (307255143777 / 78125000000) (992 / 15625)
  have hratio : ((992 / 15625) / (307255143777 / 78125000000) : ℚ) = (4960000000 / 307255143777) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV11_rounded_endpoints :
    (-1757534754680110889886975478652622479597 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV11Interval.1 ∧ manuscriptCase2Y14YV11Interval.2 ≤ (-1757534754680110811154101319005486494139 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-1757534754680110889886975478652622479597 / 10000000000000000000000000000000000000000) : ℝ) ((-1757534754680110811154101319005486494139 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1757534754680110889886975478652622479597 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV11Interval.2 : ℝ) ≤ ((-1757534754680110811154101319005486494139 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV11_exact_interval.1, manuscriptCase2Y14YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
