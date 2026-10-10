import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY13

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y13YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (325845172233521944489 / 200000000000000000000) (1900000000 / 17950910067)

private theorem manuscriptCase2Y13YV7_arg_eq : barrierCase2Y13YV7LogArg = barrierComplex (19 / 100) (-17950910067 / 10000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV7LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV7Interval.1 : ℝ) (manuscriptCase2Y13YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y13YV7LogArg).re ∈ _
  rw [manuscriptCase2Y13YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y13YV7LogArg (1) (-2) (325845172233521944489 / 200000000000000000000) (17950910067 / 5000000000) (19 / 50)
  have hratio : ((19 / 50) / (17950910067 / 5000000000) : ℚ) = (1900000000 / 17950910067) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV7_rounded_endpoints :
    (-160788231938261710066024882127636401063 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV7Interval.1 ∧ manuscriptCase2Y13YV7Interval.2 ≤ (-321576463876523392745362861166622861121 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-160788231938261710066024882127636401063 / 1250000000000000000000000000000000000000) : ℝ) ((-321576463876523392745362861166622861121 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-160788231938261710066024882127636401063 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV7Interval.2 : ℝ) ≤ ((-321576463876523392745362861166622861121 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV7_exact_interval.1, manuscriptCase2Y13YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y13YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (145438736102174247616089 / 80000000000000000000000) (5865000000 / 126986067511)

private theorem manuscriptCase2Y13YV9_arg_eq : barrierCase2Y13YV9LogArg = barrierComplex (3519 / 40000) (-380958202533 / 200000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV9LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV9Interval.1 : ℝ) (manuscriptCase2Y13YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y13YV9LogArg).re ∈ _
  rw [manuscriptCase2Y13YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y13YV9LogArg (1) (-2) (145438736102174247616089 / 80000000000000000000000) (380958202533 / 100000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (380958202533 / 100000000000) : ℚ) = (5865000000 / 126986067511) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV9_rounded_endpoints :
    (281027484981916570440006330145402957053 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV9Interval.1 ∧ manuscriptCase2Y13YV9Interval.2 ≤ (1124109939927666324967273942072092016129 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((281027484981916570440006330145402957053 / 2500000000000000000000000000000000000000) : ℝ) ((1124109939927666324967273942072092016129 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((281027484981916570440006330145402957053 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV9Interval.2 : ℝ) ≤ ((1124109939927666324967273942072092016129 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV9_exact_interval.1, manuscriptCase2Y13YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y13YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (60202114415616709854001 / 31250000000000000000000) (3968000000 / 245329104249)

private theorem manuscriptCase2Y13YV11_arg_eq : barrierCase2Y13YV11LogArg = barrierComplex (496 / 15625) (-245329104249 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y13YV11LogArg, Case2PointData.Y13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y13YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y13YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y13YV11Interval.1 : ℝ) (manuscriptCase2Y13YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y13YV11LogArg).re ∈ _
  rw [manuscriptCase2Y13YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y13YV11LogArg (1) (-2) (60202114415616709854001 / 31250000000000000000000) (245329104249 / 62500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (245329104249 / 62500000000) : ℚ) = (3968000000 / 245329104249) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y13YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y13YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y13YV11_rounded_endpoints :
    (-35146042058308864742559829874108463899 / 200000000000000000000000000000000000000) ≤ manuscriptCase2Y13YV11Interval.1 ∧ manuscriptCase2Y13YV11Interval.2 ≤ (-175730210291544315839534745705438381489 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y13YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y13YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y13 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-35146042058308864742559829874108463899 / 200000000000000000000000000000000000000) : ℝ) ((-175730210291544315839534745705438381489 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-35146042058308864742559829874108463899 / 200000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y13YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y13YV11Interval.2 : ℝ) ≤ ((-175730210291544315839534745705438381489 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y13YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y13YV11_exact_interval.1, manuscriptCase2Y13YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
