import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY11

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y11YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (117510394664871807721 / 78125000000000000000) (62500000 / 567104319)

private theorem manuscriptCase2Y11YV7_arg_eq : barrierCase2Y11YV7LogArg = barrierComplex (19 / 100) (-10774982061 / 6250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV7LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV7Interval.1 : ℝ) (manuscriptCase2Y11YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y11YV7LogArg).re ∈ _
  rw [manuscriptCase2Y11YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y11YV7LogArg (1) (-2) (117510394664871807721 / 78125000000000000000) (10774982061 / 3125000000) (19 / 50)
  have hratio : ((19 / 50) / (10774982061 / 3125000000) : ℚ) = (62500000 / 567104319) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV7_rounded_endpoints :
    (-671194060528318806472134035185683614977 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV7Interval.1 ∧ manuscriptCase2Y11YV7Interval.2 ≤ (-1342388121056637503397520930075572402207 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-671194060528318806472134035185683614977 / 5000000000000000000000000000000000000000) : ℝ) ((-1342388121056637503397520930075572402207 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-671194060528318806472134035185683614977 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV7Interval.2 : ℝ) ≤ ((-1342388121056637503397520930075572402207 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV7_exact_interval.1, manuscriptCase2Y11YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y11YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (52410471971036469660121 / 31250000000000000000000) (10996875000 / 228669063739)

private theorem manuscriptCase2Y11YV9_arg_eq : barrierCase2Y11YV9LogArg = barrierComplex (3519 / 40000) (-228669063739 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV9LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV9Interval.1 : ℝ) (manuscriptCase2Y11YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y11YV9LogArg).re ∈ _
  rw [manuscriptCase2Y11YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y11YV9LogArg (1) (-2) (52410471971036469660121 / 31250000000000000000000) (228669063739 / 62500000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (228669063739 / 62500000000) : ℚ) = (10996875000 / 228669063739) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV9_rounded_endpoints :
    (1109483649333923181156737833865563722687 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV9Interval.1 ∧ manuscriptCase2Y11YV9Interval.2 ≤ (69342728083370201522740992241926249281 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((1109483649333923181156737833865563722687 / 10000000000000000000000000000000000000000) : ℝ) ((69342728083370201522740992241926249281 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1109483649333923181156737833865563722687 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV9Interval.2 : ℝ) ≤ ((69342728083370201522740992241926249281 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV9_exact_interval.1, manuscriptCase2Y11YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y11YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (21691094930599945419889 / 12207031250000000000000) (2480000000 / 147258088167)

private theorem manuscriptCase2Y11YV11_arg_eq : barrierCase2Y11YV11LogArg = barrierComplex (496 / 15625) (-147258088167 / 78125000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV11LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV11Interval.1 : ℝ) (manuscriptCase2Y11YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y11YV11LogArg).re ∈ _
  rw [manuscriptCase2Y11YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y11YV11LogArg (1) (-2) (21691094930599945419889 / 12207031250000000000000) (147258088167 / 39062500000) (992 / 15625)
  have hratio : ((992 / 15625) / (147258088167 / 39062500000) : ℚ) = (2480000000 / 147258088167) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV11_rounded_endpoints :
    (-219053330082088351295840797001710756383 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV11Interval.1 ∧ manuscriptCase2Y11YV11Interval.2 ≤ (-1752426640656706731635089477494188391553 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-219053330082088351295840797001710756383 / 1250000000000000000000000000000000000000) : ℝ) ((-1752426640656706731635089477494188391553 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-219053330082088351295840797001710756383 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV11Interval.2 : ℝ) ≤ ((-1752426640656706731635089477494188391553 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV11_exact_interval.1, manuscriptCase2Y11YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
