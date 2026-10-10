import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV3_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV3_9Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV3_9Arg).re

def manuscriptNormV3_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) (0) (-1) (29169641 / 16000000) (371 / 7629)

private theorem manuscriptNormV3_9_arg_eq : manuscriptNormV3_9Arg = barrierComplex (1 / 1) (-3629 / 4000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_9_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_9_exact_interval :
    manuscriptNormV3_9Term ∈ Set.Icc (manuscriptNormV3_9Interval.1 : ℝ) (manuscriptNormV3_9Interval.2 : ℝ) := by
  unfold manuscriptNormV3_9Term
  rw [manuscriptNormV3_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-8254198212407 / 5000000000000000) (-14689697274259 / 5000000000000000)
    manuscriptNormV3_9Arg (0) (-1) (29169641 / 16000000) (7629 / 4000) (371 / 4000)
  have hratio : ((371 / 4000) / (7629 / 4000) : ℚ) = (371 / 7629) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_9_rounded_endpoints :
    (-1330194736875770427300979589 / 500000000000000000000000000000) ≤ manuscriptNormV3_9Interval.1 ∧ manuscriptNormV3_9Interval.2 ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_9_enclosure :
    manuscriptNormV3_9Term ∈ Set.Icc ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_9_rounded_endpoints.1
  have hhi : (manuscriptNormV3_9Interval.2 : ℝ) ≤ ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_9_exact_interval.1, manuscriptNormV3_9_exact_interval.2.trans hhi⟩

def manuscriptNormV3_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV3_10Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV3_10Arg).re

def manuscriptNormV3_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) (0) (1) (29169641 / 16000000) (-371 / 7629)

private theorem manuscriptNormV3_10_arg_eq : manuscriptNormV3_10Arg = barrierComplex (1 / 1) (3629 / 4000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_10_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_10_exact_interval :
    manuscriptNormV3_10Term ∈ Set.Icc (manuscriptNormV3_10Interval.1 : ℝ) (manuscriptNormV3_10Interval.2 : ℝ) := by
  unfold manuscriptNormV3_10Term
  rw [manuscriptNormV3_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-8254198212407 / 5000000000000000) (14689697274259 / 5000000000000000)
    manuscriptNormV3_10Arg (0) (1) (29169641 / 16000000) (7629 / 4000) (-371 / 4000)
  have hratio : ((-371 / 4000) / (7629 / 4000) : ℚ) = (-371 / 7629) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_10_rounded_endpoints :
    (-1330194736875770427300979589 / 500000000000000000000000000000) ≤ manuscriptNormV3_10Interval.1 ∧ manuscriptNormV3_10Interval.2 ≤ (-2660389473751540748094483989 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_10_enclosure :
    manuscriptNormV3_10Term ∈ Set.Icc ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1330194736875770427300979589 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_10_rounded_endpoints.1
  have hhi : (manuscriptNormV3_10Interval.2 : ℝ) ≤ ((-2660389473751540748094483989 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_10_exact_interval.1, manuscriptNormV3_10_exact_interval.2.trans hhi⟩

def manuscriptNormV3_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV3_11Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV3_11Arg).re

def manuscriptNormV3_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) (0) (-1) (11711569 / 6250000) (163 / 4837)

private theorem manuscriptNormV3_11_arg_eq : manuscriptNormV3_11Arg = barrierComplex (1 / 1) (-2337 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_11_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_11_exact_interval :
    manuscriptNormV3_11Term ∈ Set.Icc (manuscriptNormV3_11Interval.1 : ℝ) (manuscriptNormV3_11Interval.2 : ℝ) := by
  unfold manuscriptNormV3_11Term
  rw [manuscriptNormV3_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (5068806760521 / 10000000000000000) (53558167558133 / 10000000000000000)
    manuscriptNormV3_11Arg (0) (-1) (11711569 / 6250000) (4837 / 2500) (163 / 2500)
  have hratio : ((163 / 2500) / (4837 / 2500) : ℚ) = (163 / 4837) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_11_rounded_endpoints :
    (4185192971723380656657287637 / 1000000000000000000000000000000) ≤ manuscriptNormV3_11Interval.1 ∧ manuscriptNormV3_11Interval.2 ≤ (418519297172338085081844233 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV3_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_11_enclosure :
    manuscriptNormV3_11Term ∈ Set.Icc ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_11_rounded_endpoints.1
  have hhi : (manuscriptNormV3_11Interval.2 : ℝ) ≤ ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_11_exact_interval.1, manuscriptNormV3_11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
