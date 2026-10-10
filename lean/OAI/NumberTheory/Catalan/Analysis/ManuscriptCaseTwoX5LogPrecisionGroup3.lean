import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX5

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X5XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (0) (0) (19085014821803397299001 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X5XV3_arg_eq : barrierCase2X5XV3LogArg = barrierComplex (138148524501 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV3LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV3Interval.1 : ℝ) (manuscriptCase2X5XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X5XV3LogArg).re ∈ _
  rw [manuscriptCase2X5XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X5XV3LogArg (0) (0) (19085014821803397299001 / 10000000000000000000000) (138148524501 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (138148524501 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV3_rounded_endpoints :
    (-15940259829077539890238937988828500851 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV3Interval.1 ∧ manuscriptCase2X5XV3Interval.2 ≤ (-311333199786670700975441927289163791 / 19531250000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-15940259829077539890238937988828500851 / 1000000000000000000000000000000000000000) : ℝ) ((-311333199786670700975441927289163791 / 19531250000000000000000000000000000000) : ℝ) := by
  have hlo : ((-15940259829077539890238937988828500851 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV3Interval.2 : ℝ) ≤ ((-311333199786670700975441927289163791 / 19531250000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV3_exact_interval.1, manuscriptCase2X5XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (0) (0) (760316858732642791514089 / 390625000000000000000000) (0 / 1)

private theorem manuscriptCase2X5XV4_arg_eq : barrierCase2X5XV4LogArg = barrierComplex (871961500717 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV4LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV4Interval.1 : ℝ) (manuscriptCase2X5XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X5XV4LogArg).re ∈ _
  rw [manuscriptCase2X5XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X5XV4LogArg (0) (0) (760316858732642791514089 / 390625000000000000000000) (871961500717 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (871961500717 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV4_rounded_endpoints :
    (193438609393845868462192477887073548841 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV4Interval.1 ∧ manuscriptCase2X5XV4Interval.2 ≤ (77375443757538347388824818872657919397 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((193438609393845868462192477887073548841 / 5000000000000000000000000000000000000000) : ℝ) ((77375443757538347388824818872657919397 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((193438609393845868462192477887073548841 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV4Interval.2 : ℝ) ≤ ((77375443757538347388824818872657919397 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV4_exact_interval.1, manuscriptCase2X5XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (0) (68631652051963344298561 / 62500000000000000000000) (78304866081 / 250000000000)

private theorem manuscriptCase2X5XV5_arg_eq : barrierCase2X5XV5LogArg = barrierComplex (1 / 1) (78304866081 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV5LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV5Interval.1 : ℝ) (manuscriptCase2X5XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X5XV5LogArg).re ∈ _
  rw [manuscriptCase2X5XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X5XV5LogArg (0) (0) (68631652051963344298561 / 62500000000000000000000) (1 / 1) (78304866081 / 250000000000)
  have hratio : ((78304866081 / 250000000000) / (1 / 1) : ℚ) = (78304866081 / 250000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV5_rounded_endpoints :
    (-519794764954649642222648507968680681831 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV5Interval.1 ∧ manuscriptCase2X5XV5Interval.2 ≤ (-103958952990929928444529700040400405557 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-519794764954649642222648507968680681831 / 10000000000000000000000000000000000000000) : ℝ) ((-103958952990929928444529700040400405557 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-519794764954649642222648507968680681831 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV5Interval.2 : ℝ) ≤ ((-103958952990929928444529700040400405557 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV5_exact_interval.1, manuscriptCase2X5XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
