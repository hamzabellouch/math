import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV6_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV6_0Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV6_0Arg).re

def manuscriptNormV6_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) (0) (-1) (21709 / 15625) (47 / 203)

private theorem manuscriptNormV6_0_arg_eq : manuscriptNormV6_0Arg = barrierComplex (1 / 1) (-78 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_0_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_0_exact_interval :
    manuscriptNormV6_0Term ∈ Set.Icc (manuscriptNormV6_0Interval.1 : ℝ) (manuscriptNormV6_0Interval.2 : ℝ) := by
  unfold manuscriptNormV6_0Term
  rw [manuscriptNormV6_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-207003480727327 / 10000000000000000) (9130910809039 / 312500000000000)
    manuscriptNormV6_0Arg (0) (-1) (21709 / 15625) (203 / 125) (47 / 125)
  have hratio : ((47 / 125) / (203 / 125) : ℚ) = (47 / 203) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_0_rounded_endpoints :
    (12896941244777008109092538609 / 1000000000000000000000000000000) ≤ manuscriptNormV6_0Interval.1 ∧ manuscriptNormV6_0Interval.2 ≤ (1612117655597126146042737969 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV6_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_0_enclosure :
    manuscriptNormV6_0Term ∈ Set.Icc ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((12896941244777008109092538609 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_0_rounded_endpoints.1
  have hhi : (manuscriptNormV6_0Interval.2 : ℝ) ≤ ((1612117655597126146042737969 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_0_exact_interval.1, manuscriptNormV6_0_exact_interval.2.trans hhi⟩

def manuscriptNormV6_1Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 1 (0, 0)).1

def manuscriptNormV6_1Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormV6_1Arg).re

def manuscriptNormV6_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) (0) (-1) (609649 / 390625) (157 / 1093)

private theorem manuscriptNormV6_1_arg_eq : manuscriptNormV6_1Arg = barrierComplex (1 / 1) (-468 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_1Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_1_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_1_exact_interval :
    manuscriptNormV6_1Term ∈ Set.Icc (manuscriptNormV6_1Interval.1 : ℝ) (manuscriptNormV6_1Interval.2 : ℝ) := by
  unfold manuscriptNormV6_1Term
  rw [manuscriptNormV6_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-30314387010667 / 5000000000000000) (1337165747419 / 156250000000000)
    manuscriptNormV6_1Arg (0) (-1) (609649 / 390625) (1093 / 625) (157 / 625)
  have hratio : ((157 / 625) / (1093 / 625) : ℚ) = (157 / 1093) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_1Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_1_rounded_endpoints :
    (518877014766705861242949901 / 125000000000000000000000000000) ≤ manuscriptNormV6_1Interval.1 ∧ manuscriptNormV6_1Interval.2 ≤ (1037754029533411800046178233 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV6_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_1_enclosure :
    manuscriptNormV6_1Term ∈ Set.Icc ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((518877014766705861242949901 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_1_rounded_endpoints.1
  have hhi : (manuscriptNormV6_1Interval.2 : ℝ) ≤ ((1037754029533411800046178233 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_1_exact_interval.1, manuscriptNormV6_1_exact_interval.2.trans hhi⟩

def manuscriptNormV6_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 6 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV6_2Term : ℝ :=
  (-((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV6_2Arg).re

def manuscriptNormV6_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) (0) (1) (574666 / 390625) (-98 / 527)

private theorem manuscriptNormV6_2_arg_eq : manuscriptNormV6_2Arg = barrierComplex (1 / 1) (429 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV6_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV6_2_weight_eq :
    -((barrierV2Tail.getD 6 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV6_2_exact_interval :
    manuscriptNormV6_2Term ∈ Set.Icc (manuscriptNormV6_2Interval.1 : ℝ) (manuscriptNormV6_2Interval.2 : ℝ) := by
  unfold manuscriptNormV6_2Term
  rw [manuscriptNormV6_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-17333342034543 / 5000000000000000) (764572651551 / 156250000000000)
    manuscriptNormV6_2Arg (0) (1) (574666 / 390625) (1054 / 625) (-196 / 625)
  have hratio : ((-196 / 625) / (1054 / 625) : ℚ) = (-98 / 527) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV6_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV6_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV6_2_rounded_endpoints :
    (-722526542219310315268128121 / 200000000000000000000000000000) ≤ manuscriptNormV6_2Interval.1 ∧ manuscriptNormV6_2Interval.2 ≤ (-903158177774137849737278943 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV6_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV6_2_enclosure :
    manuscriptNormV6_2Term ∈ Set.Icc ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-722526542219310315268128121 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV6_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_2_rounded_endpoints.1
  have hhi : (manuscriptNormV6_2Interval.2 : ℝ) ≤ ((-903158177774137849737278943 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV6_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV6_2_exact_interval.1, manuscriptNormV6_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
