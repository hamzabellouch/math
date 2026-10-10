import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP3_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP3_7Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP3_7Arg).re

def manuscriptNormP3_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-249342691992771 / 20000000000000000) (244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP3_7_arg_eq : manuscriptNormP3_7Arg = barrierComplex (411 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_7_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-249342691992771 / 20000000000000000) (244406797738203 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_7_exact_interval :
    manuscriptNormP3_7Term ∈ Set.Icc (manuscriptNormP3_7Interval.1 : ℝ) (manuscriptNormP3_7Interval.2 : ℝ) := by
  unfold manuscriptNormP3_7Term
  rw [manuscriptNormP3_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-249342691992771 / 20000000000000000) (244406797738203 / 20000000000000000)
    manuscriptNormP3_7Arg (1) (0) (16918021 / 12500000) (411 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (411 / 250) : ℚ) = (161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_7_rounded_endpoints :
    (-6685833039281012505245132349 / 1000000000000000000000000000000) ≤ manuscriptNormP3_7Interval.1 ∧ manuscriptNormP3_7Interval.2 ≤ (-6685833039281012504403289509 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP3_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_7_enclosure :
    manuscriptNormP3_7Term ∈ Set.Icc ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_7_rounded_endpoints.1
  have hhi : (manuscriptNormP3_7Interval.2 : ℝ) ≤ ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_7_exact_interval.1, manuscriptNormP3_7_exact_interval.2.trans hhi⟩

def manuscriptNormP3_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP3_8Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP3_8Arg).re

def manuscriptNormP3_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP3_8_arg_eq : manuscriptNormP3_8Arg = barrierComplex (89 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_8_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_8_exact_interval :
    manuscriptNormP3_8Term ∈ Set.Icc (manuscriptNormP3_8Interval.1 : ℝ) (manuscriptNormP3_8Interval.2 : ℝ) := by
  unfold manuscriptNormP3_8Term
  rw [manuscriptNormP3_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000)
    manuscriptNormP3_8Arg (-3) (0) (818021 / 781250) (89 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (89 / 250) : ℚ) = (-161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_8_rounded_endpoints :
    (3328926488531865759414963479 / 250000000000000000000000000000) ≤ manuscriptNormP3_8Interval.1 ∧ manuscriptNormP3_8Interval.2 ≤ (1664463244265932879979458429 / 125000000000000000000000000000) := by
  simp only [manuscriptNormP3_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_8_enclosure :
    manuscriptNormP3_8Term ∈ Set.Icc ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_8_rounded_endpoints.1
  have hhi : (manuscriptNormP3_8Interval.2 : ℝ) ≤ ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_8_exact_interval.1, manuscriptNormP3_8_exact_interval.2.trans hhi⟩

def manuscriptNormP3_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP3_9Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP3_9Arg).re

def manuscriptNormP3_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (150530316475111 / 40000000000000000) (-334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP3_9_arg_eq : manuscriptNormP3_9Arg = barrierComplex (411 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_9_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (150530316475111 / 40000000000000000) (-334867072933799 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_9_exact_interval :
    manuscriptNormP3_9Term ∈ Set.Icc (manuscriptNormP3_9Interval.1 : ℝ) (manuscriptNormP3_9Interval.2 : ℝ) := by
  unfold manuscriptNormP3_9Term
  rw [manuscriptNormP3_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (150530316475111 / 40000000000000000) (-334867072933799 / 20000000000000000)
    manuscriptNormP3_9Arg (1) (0) (16918021 / 12500000) (411 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (411 / 250) : ℚ) = (-161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_9_rounded_endpoints :
    (1218174183467901772278121067 / 1000000000000000000000000000000) ≤ manuscriptNormP3_9Interval.1 ∧ manuscriptNormP3_9Interval.2 ≤ (121817418346790177253223493 / 100000000000000000000000000000) := by
  simp only [manuscriptNormP3_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_9_enclosure :
    manuscriptNormP3_9Term ∈ Set.Icc ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_9_rounded_endpoints.1
  have hhi : (manuscriptNormP3_9Interval.2 : ℝ) ≤ ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_9_exact_interval.1, manuscriptNormP3_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
