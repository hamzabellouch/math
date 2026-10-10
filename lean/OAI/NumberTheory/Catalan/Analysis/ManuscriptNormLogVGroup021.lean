import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV4_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV4_11Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV4_11Arg).re

def manuscriptNormV4_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377)

private theorem manuscriptNormV4_11_arg_eq : manuscriptNormV4_11Arg = barrierComplex (1 / 1) (-15129 / 15625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_11_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_11_exact_interval :
    manuscriptNormV4_11Term ∈ Set.Icc (manuscriptNormV4_11Interval.1 : ℝ) (manuscriptNormV4_11Interval.2 : ℝ) := by
  unfold manuscriptNormV4_11Term
  rw [manuscriptNormV4_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000)
    manuscriptNormV4_11Arg (0) (-1) (473027266 / 244140625) (30754 / 15625) (496 / 15625)
  have hratio : ((496 / 15625) / (30754 / 15625) : ℚ) = (248 / 15377) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_11_rounded_endpoints :
    (-5049556952780585057360689577 / 500000000000000000000000000000) ≤ manuscriptNormV4_11Interval.1 ∧ manuscriptNormV4_11Interval.2 ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_11_enclosure :
    manuscriptNormV4_11Term ∈ Set.Icc ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_11_rounded_endpoints.1
  have hhi : (manuscriptNormV4_11Interval.2 : ℝ) ≤ ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_11_exact_interval.1, manuscriptNormV4_11_exact_interval.2.trans hhi⟩

def manuscriptNormV4_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 4 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV4_12Term : ℝ :=
  (-((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV4_12Arg).re

def manuscriptNormV4_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377)

private theorem manuscriptNormV4_12_arg_eq : manuscriptNormV4_12Arg = barrierComplex (1 / 1) (15129 / 15625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV4_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV4_12_weight_eq :
    -((barrierV2Tail.getD 4 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV4_12_exact_interval :
    manuscriptNormV4_12Term ∈ Set.Icc (manuscriptNormV4_12Interval.1 : ℝ) (manuscriptNormV4_12Interval.2 : ℝ) := by
  unfold manuscriptNormV4_12Term
  rw [manuscriptNormV4_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000)
    manuscriptNormV4_12Arg (0) (1) (473027266 / 244140625) (30754 / 15625) (-496 / 15625)
  have hratio : ((-496 / 15625) / (30754 / 15625) : ℚ) = (-248 / 15377) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV4_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV4_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV4_12_rounded_endpoints :
    (-5049556952780585057360689577 / 500000000000000000000000000000) ≤ manuscriptNormV4_12Interval.1 ∧ manuscriptNormV4_12Interval.2 ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV4_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV4_12_enclosure :
    manuscriptNormV4_12Term ∈ Set.Icc ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV4_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_12_rounded_endpoints.1
  have hhi : (manuscriptNormV4_12Interval.2 : ℝ) ≤ ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV4_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV4_12_exact_interval.1, manuscriptNormV4_12_exact_interval.2.trans hhi⟩

def manuscriptNormV5_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 5 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV5_0Term : ℝ :=
  (-((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV5_0Arg).re

def manuscriptNormV5_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) (0) (1) (21709 / 15625) (-47 / 203)

private theorem manuscriptNormV5_0_arg_eq : manuscriptNormV5_0Arg = barrierComplex (1 / 1) (78 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV5_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV5_0_weight_eq :
    -((barrierV2Tail.getD 5 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV5_0_exact_interval :
    manuscriptNormV5_0Term ∈ Set.Icc (manuscriptNormV5_0Interval.1 : ℝ) (manuscriptNormV5_0Interval.2 : ℝ) := by
  unfold manuscriptNormV5_0Term
  rw [manuscriptNormV5_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-207003480727327 / 10000000000000000) (-9130910809039 / 312500000000000)
    manuscriptNormV5_0Arg (0) (1) (21709 / 15625) (203 / 125) (-47 / 125)
  have hratio : ((-47 / 125) / (203 / 125) : ℚ) = (-47 / 203) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV5_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV5_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV5_0_rounded_endpoints :
    (12896941244777008109092538609 / 1000000000000000000000000000000) ≤ manuscriptNormV5_0Interval.1 ∧ manuscriptNormV5_0Interval.2 ≤ (1612117655597126146042737969 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV5_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV5_0_enclosure :
    manuscriptNormV5_0Term ∈ Set.Icc ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV5_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_0_rounded_endpoints.1
  have hhi : (manuscriptNormV5_0Interval.2 : ℝ) ≤ ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV5_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV5_0_exact_interval.1, manuscriptNormV5_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
