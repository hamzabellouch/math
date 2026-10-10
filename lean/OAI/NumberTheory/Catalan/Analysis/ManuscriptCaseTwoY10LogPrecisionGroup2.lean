import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY10

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y10YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (6473195881655022554281 / 5000000000000000000000) (9500000000 / 79893340659)

private theorem manuscriptCase2Y10YV7_arg_eq : barrierCase2Y10YV7LogArg = barrierComplex (19 / 100) (-79893340659 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV7LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV7Interval.1 : ℝ) (manuscriptCase2Y10YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y10YV7LogArg).re ∈ _
  rw [manuscriptCase2Y10YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y10YV7LogArg (1) (-2) (6473195881655022554281 / 5000000000000000000000) (79893340659 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (79893340659 / 25000000000) : ℚ) = (9500000000 / 79893340659) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV7_rounded_endpoints :
    (-1446943924969308980878733752317009028077 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV7Interval.1 ∧ manuscriptCase2Y10YV7Interval.2 ≤ (-361735981242327217832996653198784564587 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-1446943924969308980878733752317009028077 / 10000000000000000000000000000000000000000) : ℝ) ((-361735981242327217832996653198784564587 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1446943924969308980878733752317009028077 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV7Interval.2 : ℝ) ≤ ((-361735981242327217832996653198784564587 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV7_exact_interval.1, manuscriptCase2Y10YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y10YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2882508103201010837070681 / 2000000000000000000000000) (9775000000 / 188390469949)

private theorem manuscriptCase2Y10YV9_arg_eq : barrierCase2Y10YV9LogArg = barrierComplex (3519 / 40000) (-1695514229541 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV9LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV9Interval.1 : ℝ) (manuscriptCase2Y10YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y10YV9LogArg).re ∈ _
  rw [manuscriptCase2Y10YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y10YV9LogArg (1) (-2) (2882508103201010837070681 / 2000000000000000000000000) (1695514229541 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1695514229541 / 500000000000) : ℚ) = (9775000000 / 188390469949) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV9_rounded_endpoints :
    (270466046719760345800886206589476937391 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV9Interval.1 ∧ manuscriptCase2Y10YV9Interval.2 ≤ (16904127919985022287666595011473878657 / 156250000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((270466046719760345800886206589476937391 / 2500000000000000000000000000000000000000) : ℝ) ((16904127919985022287666595011473878657 / 156250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((270466046719760345800886206589476937391 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV9Interval.2 : ℝ) ≤ ((16904127919985022287666595011473878657 / 156250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV9_exact_interval.1, manuscriptCase2Y10YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y10YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1192586073051343657082929 / 781250000000000000000000) (19840000000 / 1091875655673)

private theorem manuscriptCase2Y10YV11_arg_eq : barrierCase2Y10YV11LogArg = barrierComplex (496 / 15625) (-1091875655673 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y10YV11LogArg, Case2PointData.Y10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y10YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y10YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y10YV11Interval.1 : ℝ) (manuscriptCase2Y10YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y10YV11LogArg).re ∈ _
  rw [manuscriptCase2Y10YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y10YV11LogArg (1) (-2) (1192586073051343657082929 / 781250000000000000000000) (1091875655673 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (1091875655673 / 312500000000) : ℚ) = (19840000000 / 1091875655673) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y10YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y10YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y10YV11_rounded_endpoints :
    (-1743178691306224448925451335187547835883 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y10YV11Interval.1 ∧ manuscriptCase2Y10YV11Interval.2 ≤ (-1743178691306224370193824700551673848817 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y10YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y10YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y10 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-1743178691306224448925451335187547835883 / 10000000000000000000000000000000000000000) : ℝ) ((-1743178691306224370193824700551673848817 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1743178691306224448925451335187547835883 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y10YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y10YV11Interval.2 : ℝ) ≤ ((-1743178691306224370193824700551673848817 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y10YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y10YV11_exact_interval.1, manuscriptCase2Y10YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
