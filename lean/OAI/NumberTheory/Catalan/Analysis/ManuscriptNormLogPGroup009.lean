import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP2_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP2_8Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP2_8Arg).re

def manuscriptNormP2_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP2_8_arg_eq : manuscriptNormP2_8Arg = barrierComplex (411 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_8_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_8_exact_interval :
    manuscriptNormP2_8Term ∈ Set.Icc (manuscriptNormP2_8Interval.1 : ℝ) (manuscriptNormP2_8Interval.2 : ℝ) := by
  unfold manuscriptNormP2_8Term
  rw [manuscriptNormP2_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000)
    manuscriptNormP2_8Arg (1) (0) (16918021 / 12500000) (411 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (411 / 250) : ℚ) = (161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_8_rounded_endpoints :
    (1218174183467901772278121067 / 1000000000000000000000000000000) ≤ manuscriptNormP2_8Interval.1 ∧ manuscriptNormP2_8Interval.2 ≤ (121817418346790177253223493 / 100000000000000000000000000000) := by
  simp only [manuscriptNormP2_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_8_enclosure :
    manuscriptNormP2_8Term ∈ Set.Icc ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_8_rounded_endpoints.1
  have hhi : (manuscriptNormP2_8Interval.2 : ℝ) ≤ ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_8_exact_interval.1, manuscriptNormP2_8_exact_interval.2.trans hhi⟩

def manuscriptNormP2_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP2_9Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP2_9Arg).re

def manuscriptNormP2_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP2_9_arg_eq : manuscriptNormP2_9Arg = barrierComplex (89 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_9_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_9_exact_interval :
    manuscriptNormP2_9Term ∈ Set.Icc (manuscriptNormP2_9Interval.1 : ℝ) (manuscriptNormP2_9Interval.2 : ℝ) := by
  unfold manuscriptNormP2_9Term
  rw [manuscriptNormP2_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000)
    manuscriptNormP2_9Arg (-3) (0) (818021 / 781250) (89 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (89 / 250) : ℚ) = (161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_9_rounded_endpoints :
    (3328926488531865759414963479 / 250000000000000000000000000000) ≤ manuscriptNormP2_9Interval.1 ∧ manuscriptNormP2_9Interval.2 ≤ (1664463244265932879979458429 / 125000000000000000000000000000) := by
  simp only [manuscriptNormP2_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_9_enclosure :
    manuscriptNormP2_9Term ∈ Set.Icc ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_9_rounded_endpoints.1
  have hhi : (manuscriptNormP2_9Interval.2 : ℝ) ≤ ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_9_exact_interval.1, manuscriptNormP2_9_exact_interval.2.trans hhi⟩

def manuscriptNormP3_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP3_0Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP3_0Arg).re

def manuscriptNormP3_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) (0) (1) (54161 / 40000) (-81 / 319)

private theorem manuscriptNormP3_0_arg_eq : manuscriptNormP3_0Arg = barrierComplex (1 / 1) (119 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_0_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_0_exact_interval :
    manuscriptNormP3_0Term ∈ Set.Icc (manuscriptNormP3_0Interval.1 : ℝ) (manuscriptNormP3_0Interval.2 : ℝ) := by
  unfold manuscriptNormP3_0Term
  rw [manuscriptNormP3_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-77366649157093 / 2500000000000000) (-74491825385797 / 5000000000000000)
    manuscriptNormP3_0Arg (0) (1) (54161 / 40000) (319 / 200) (-81 / 200)
  have hratio : ((-81 / 200) / (319 / 200) : ℚ) = (-81 / 319) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_0_rounded_endpoints :
    (661358122763075158075038643 / 200000000000000000000000000000) ≤ manuscriptNormP3_0Interval.1 ∧ manuscriptNormP3_0Interval.2 ≤ (826697653453844082618353217 / 250000000000000000000000000000) := by
  simp only [manuscriptNormP3_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_0_enclosure :
    manuscriptNormP3_0Term ∈ Set.Icc ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_0_rounded_endpoints.1
  have hhi : (manuscriptNormP3_0Interval.2 : ℝ) ≤ ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_0_exact_interval.1, manuscriptNormP3_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
