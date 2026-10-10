import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX10

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X10XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (10347898357825873699321 / 10000000000000000000000) (-18652033611 / 100000000000)

private theorem manuscriptCase2X10XV7_arg_eq : barrierCase2X10XV7LogArg = barrierComplex (1 / 1) (-18652033611 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV7LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV7Interval.1 : ℝ) (manuscriptCase2X10XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X10XV7LogArg).re ∈ _
  rw [manuscriptCase2X10XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X10XV7LogArg (0) (0) (10347898357825873699321 / 10000000000000000000000) (1 / 1) (-18652033611 / 100000000000)
  have hratio : ((-18652033611 / 100000000000) / (1 / 1) : ℚ) = (-18652033611 / 100000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV7_rounded_endpoints :
    (125773685977529363927645602228655563413 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X10XV7Interval.1 ∧ manuscriptCase2X10XV7Interval.2 ≤ (62886842988764681963822801114327781721 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((125773685977529363927645602228655563413 / 5000000000000000000000000000000000000000) : ℝ) ((62886842988764681963822801114327781721 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((125773685977529363927645602228655563413 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV7Interval.2 : ℝ) ≤ ((62886842988764681963822801114327781721 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV7_exact_interval.1, manuscriptCase2X10XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (4156687407306737017591721 / 4000000000000000000000000) (-395837602189 / 2000000000000)

private theorem manuscriptCase2X10XV9_arg_eq : barrierCase2X10XV9LogArg = barrierComplex (1 / 1) (-395837602189 / 2000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV9LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV9Interval.1 : ℝ) (manuscriptCase2X10XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X10XV9LogArg).re ∈ _
  rw [manuscriptCase2X10XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X10XV9LogArg (0) (0) (4156687407306737017591721 / 4000000000000000000000000) (1 / 1) (-395837602189 / 2000000000000)
  have hratio : ((-395837602189 / 2000000000000) / (1 / 1) : ℚ) = (-395837602189 / 2000000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV9_rounded_endpoints :
    (-15351093478685753782612901723332059597 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X10XV9Interval.1 ∧ manuscriptCase2X10XV9Interval.2 ≤ (-24561749565897206052180642757331295273 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-15351093478685753782612901723332059597 / 1250000000000000000000000000000000000000) : ℝ) ((-24561749565897206052180642757331295273 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-15351093478685753782612901723332059597 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV9Interval.2 : ℝ) ≤ ((-24561749565897206052180642757331295273 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV9_exact_interval.1, manuscriptCase2X10XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (1627479682167254854284289 / 1562500000000000000000000) (-254911126017 / 1250000000000)

private theorem manuscriptCase2X10XV11_arg_eq : barrierCase2X10XV11LogArg = barrierComplex (1 / 1) (-254911126017 / 1250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV11LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV11Interval.1 : ℝ) (manuscriptCase2X10XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X10XV11LogArg).re ∈ _
  rw [manuscriptCase2X10XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X10XV11LogArg (0) (0) (1627479682167254854284289 / 1562500000000000000000000) (1 / 1) (-254911126017 / 1250000000000)
  have hratio : ((-254911126017 / 1250000000000) / (1 / 1) : ℚ) = (-254911126017 / 1250000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV11_rounded_endpoints :
    (6891340771826401379354009018102878867 / 312500000000000000000000000000000000000) ≤ manuscriptCase2X10XV11Interval.1 ∧ manuscriptCase2X10XV11Interval.2 ≤ (220522904698444844139328288579292126981 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((6891340771826401379354009018102878867 / 312500000000000000000000000000000000000) : ℝ) ((220522904698444844139328288579292126981 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((6891340771826401379354009018102878867 / 312500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV11Interval.2 : ℝ) ≤ ((220522904698444844139328288579292126981 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV11_exact_interval.1, manuscriptCase2X10XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
