import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX5

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X5XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2826537683240651471521 / 2500000000000000000000) (18070353711 / 50000000000)

private theorem manuscriptCase2X5XV7_arg_eq : barrierCase2X5XV7LogArg = barrierComplex (1 / 1) (18070353711 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV7LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV7Interval.1 : ℝ) (manuscriptCase2X5XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X5XV7LogArg).re ∈ _
  rw [manuscriptCase2X5XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X5XV7LogArg (0) (0) (2826537683240651471521 / 2500000000000000000000) (1 / 1) (18070353711 / 50000000000)
  have hratio : ((18070353711 / 50000000000) / (1 / 1) : ℚ) = (18070353711 / 50000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV7_rounded_endpoints :
    (-61966174194982187608732524678148418713 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV7Interval.1 ∧ manuscriptCase2X5XV7Interval.2 ≤ (-123932348389964375217463695771769802981 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-61966174194982187608732524678148418713 / 1000000000000000000000000000000000000000) : ℝ) ((-123932348389964375217463695771769802981 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-61966174194982187608732524678148418713 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV7Interval.2 : ℝ) ≤ ((-123932348389964375217463695771769802981 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV7_exact_interval.1, manuscriptCase2X5XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (383493062089 / 1000000000000)

private theorem manuscriptCase2X5XV9_arg_eq : barrierCase2X5XV9LogArg = barrierComplex (1 / 1) (383493062089 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV9LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV9Interval.1 : ℝ) (manuscriptCase2X5XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X5XV9LogArg).re ∈ _
  rw [manuscriptCase2X5XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X5XV9LogArg (0) (0) (1147066928670397609043921 / 1000000000000000000000000) (1 / 1) (383493062089 / 1000000000000)
  have hratio : ((383493062089 / 1000000000000) / (1 / 1) : ℚ) = (383493062089 / 1000000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV9_rounded_endpoints :
    (39030126788942082198174297447646242529 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV9Interval.1 ∧ manuscriptCase2X5XV9Interval.2 ≤ (9757531697235520549546016982038402291 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((39030126788942082198174297447646242529 / 2000000000000000000000000000000000000000) : ℝ) ((9757531697235520549546016982038402291 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((39030126788942082198174297447646242529 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV9Interval.2 : ℝ) ≤ ((9757531697235520549546016982038402291 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV9_exact_interval.1, manuscriptCase2X5XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (451614982836392791514089 / 390625000000000000000000) (246961500717 / 625000000000)

private theorem manuscriptCase2X5XV11_arg_eq : barrierCase2X5XV11LogArg = barrierComplex (1 / 1) (246961500717 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XV11LogArg, Case2PointData.X5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XV11Interval.1 : ℝ) (manuscriptCase2X5XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X5XV11LogArg).re ∈ _
  rw [manuscriptCase2X5XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X5XV11LogArg (0) (0) (451614982836392791514089 / 390625000000000000000000) (1 / 1) (246961500717 / 625000000000)
  have hratio : ((246961500717 / 625000000000) / (1 / 1) : ℚ) = (246961500717 / 625000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XV11_rounded_endpoints :
    (-401138384494284021583895239422833884051 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XV11Interval.1 ∧ manuscriptCase2X5XV11Interval.2 ≤ (-200569192247142010791754763595965225083 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-401138384494284021583895239422833884051 / 10000000000000000000000000000000000000000) : ℝ) ((-200569192247142010791754763595965225083 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-401138384494284021583895239422833884051 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XV11Interval.2 : ℝ) ≤ ((-200569192247142010791754763595965225083 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XV11_exact_interval.1, manuscriptCase2X5XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
