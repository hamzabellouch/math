import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP8_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP8_2Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP8_2Arg).re

def manuscriptNormP8_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP8_2_arg_eq : manuscriptNormP8_2Arg = barrierComplex (411 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_2_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_2_exact_interval :
    manuscriptNormP8_2Term ∈ Set.Icc (manuscriptNormP8_2Interval.1 : ℝ) (manuscriptNormP8_2Interval.2 : ℝ) := by
  unfold manuscriptNormP8_2Term
  rw [manuscriptNormP8_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (150530316475111 / 40000000000000000) (334867072933799 / 20000000000000000)
    manuscriptNormP8_2Arg (1) (0) (16918021 / 12500000) (411 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (411 / 250) : ℚ) = (161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_2_rounded_endpoints :
    (1218174183467901772278121067 / 1000000000000000000000000000000) ≤ manuscriptNormP8_2Interval.1 ∧ manuscriptNormP8_2Interval.2 ≤ (121817418346790177253223493 / 100000000000000000000000000000) := by
  simp only [manuscriptNormP8_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_2_enclosure :
    manuscriptNormP8_2Term ∈ Set.Icc ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_2_rounded_endpoints.1
  have hhi : (manuscriptNormP8_2Interval.2 : ℝ) ≤ ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_2_exact_interval.1, manuscriptNormP8_2_exact_interval.2.trans hhi⟩

def manuscriptNormP8_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP8_3Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP8_3Arg).re

def manuscriptNormP8_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (-161 / 890)

private theorem manuscriptNormP8_3_arg_eq : manuscriptNormP8_3Arg = barrierComplex (89 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_3_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_3_exact_interval :
    manuscriptNormP8_3Term ∈ Set.Icc (manuscriptNormP8_3Interval.1 : ℝ) (manuscriptNormP8_3Interval.2 : ℝ) := by
  unfold manuscriptNormP8_3Term
  rw [manuscriptNormP8_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-85926283605499 / 8000000000000000) (53536907546363 / 4000000000000000)
    manuscriptNormP8_3Arg (-3) (0) (818021 / 781250) (89 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (89 / 250) : ℚ) = (-161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_3_rounded_endpoints :
    (3328926488531865759414963479 / 250000000000000000000000000000) ≤ manuscriptNormP8_3Interval.1 ∧ manuscriptNormP8_3Interval.2 ≤ (1664463244265932879979458429 / 125000000000000000000000000000) := by
  simp only [manuscriptNormP8_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_3_enclosure :
    manuscriptNormP8_3Term ∈ Set.Icc ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_3_rounded_endpoints.1
  have hhi : (manuscriptNormP8_3Interval.2 : ℝ) ≤ ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_3_exact_interval.1, manuscriptNormP8_3_exact_interval.2.trans hhi⟩

def manuscriptNormP8_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP8_4Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP8_4Arg).re

def manuscriptNormP8_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP8_4_arg_eq : manuscriptNormP8_4Arg = barrierComplex (891 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_4_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_4_exact_interval :
    manuscriptNormP8_4Term ∈ Set.Icc (manuscriptNormP8_4Interval.1 : ℝ) (manuscriptNormP8_4Interval.2 : ℝ) := by
  unfold manuscriptNormP8_4Term
  rw [manuscriptNormP8_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000)
    manuscriptNormP8_4Arg (1) (0) (79540981 / 50000000) (891 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (891 / 500) : ℚ) = (391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_4_rounded_endpoints :
    (-825452530567521026167866743 / 1000000000000000000000000000000) ≤ manuscriptNormP8_4Interval.1 ∧ manuscriptNormP8_4Interval.2 ≤ (-412726265283760513035682481 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP8_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_4_enclosure :
    manuscriptNormP8_4Term ∈ Set.Icc ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_4_rounded_endpoints.1
  have hhi : (manuscriptNormP8_4Interval.2 : ℝ) ≤ ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_4_exact_interval.1, manuscriptNormP8_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
