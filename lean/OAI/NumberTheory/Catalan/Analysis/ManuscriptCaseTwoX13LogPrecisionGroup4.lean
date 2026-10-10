import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX13

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X13XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (12773306022934549459681 / 10000000000000000000000) (47337812209 / 152662187791)

private theorem manuscriptCase2X13XV7_arg_eq : barrierCase2X13XV7LogArg = barrierComplex (1 / 1) (-52662187791 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV7LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV7Interval.1 : ℝ) (manuscriptCase2X13XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X13XV7LogArg).re ∈ _
  rw [manuscriptCase2X13XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X13XV7LogArg (0) (-1) (12773306022934549459681 / 10000000000000000000000) (152662187791 / 100000000000) (47337812209 / 100000000000)
  have hratio : ((47337812209 / 100000000000) / (152662187791 / 100000000000) : ℚ) = (47337812209 / 152662187791) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV7_rounded_endpoints :
    (107973189159864953450627026925846674967 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV7Interval.1 ∧ manuscriptCase2X13XV7Interval.2 ≤ (539865945799324821973601067378922544917 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((107973189159864953450627026925846674967 / 2000000000000000000000000000000000000000) : ℝ) ((539865945799324821973601067378922544917 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((107973189159864953450627026925846674967 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV7Interval.2 : ℝ) ≤ ((539865945799324821973601067378922544917 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV7_exact_interval.1, manuscriptCase2X13XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (5249049099045374059736081 / 4000000000000000000000000) (882391347991 / 3117608652009)

private theorem manuscriptCase2X13XV9_arg_eq : barrierCase2X13XV9LogArg = barrierComplex (1 / 1) (-1117608652009 / 2000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV9LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV9Interval.1 : ℝ) (manuscriptCase2X13XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X13XV9LogArg).re ∈ _
  rw [manuscriptCase2X13XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X13XV9LogArg (0) (-1) (5249049099045374059736081 / 4000000000000000000000000) (3117608652009 / 2000000000000) (882391347991 / 2000000000000)
  have hratio : ((882391347991 / 2000000000000) / (3117608652009 / 2000000000000) : ℚ) = (882391347991 / 3117608652009) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV9_rounded_endpoints :
    (-174492795299641448384464768773163114119 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV9Interval.1 ∧ manuscriptCase2X13XV9Interval.2 ≤ (-6979711811985657503533408804617100203 / 200000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-174492795299641448384464768773163114119 / 5000000000000000000000000000000000000000) : ℝ) ((-6979711811985657503533408804617100203 / 200000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-174492795299641448384464768773163114119 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV9Interval.2 : ℝ) ≤ ((-6979711811985657503533408804617100203 / 200000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV9_exact_interval.1, manuscriptCase2X13XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2080491936061441960191529 / 1562500000000000000000000) (530283433523 / 1969716566477)

private theorem manuscriptCase2X13XV11_arg_eq : barrierCase2X13XV11LogArg = barrierComplex (1 / 1) (-719716566477 / 1250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV11LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV11Interval.1 : ℝ) (manuscriptCase2X13XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X13XV11LogArg).re ∈ _
  rw [manuscriptCase2X13XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X13XV11LogArg (0) (-1) (2080491936061441960191529 / 1562500000000000000000000) (1969716566477 / 1250000000000) (530283433523 / 1250000000000)
  have hratio : ((530283433523 / 1250000000000) / (1969716566477 / 1250000000000) : ℚ) = (530283433523 / 1969716566477) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV11_rounded_endpoints :
    (116389112157030378544029504189985378087 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV11Interval.1 ∧ manuscriptCase2X13XV11Interval.2 ≤ (581945560785151932082491383483916465491 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((116389112157030378544029504189985378087 / 2000000000000000000000000000000000000000) : ℝ) ((581945560785151932082491383483916465491 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((116389112157030378544029504189985378087 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV11Interval.2 : ℝ) ≤ ((581945560785151932082491383483916465491 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV11_exact_interval.1, manuscriptCase2X13XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
