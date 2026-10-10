import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP9_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP9_1Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP9_1Arg).re

def manuscriptNormP9_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391)

private theorem manuscriptNormP9_1_arg_eq : manuscriptNormP9_1Arg = barrierComplex (13581 / 12500) (1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_1_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_1_exact_interval :
    manuscriptNormP9_1Term ∈ Set.Icc (manuscriptNormP9_1Interval.1 : ℝ) (manuscriptNormP9_1Interval.2 : ℝ) := by
  unfold manuscriptNormP9_1Term
  rw [manuscriptNormP9_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000)
    manuscriptNormP9_1Arg (0) (1) (301299661 / 156250000) (24391 / 12500) (-2771 / 12500)
  have hratio : ((-2771 / 12500) / (24391 / 12500) : ℚ) = (-2771 / 24391) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_1_rounded_endpoints :
    (29020409128306298718006873 / 50000000000000000000000000000) ≤ manuscriptNormP9_1Interval.1 ∧ manuscriptNormP9_1Interval.2 ≤ (580408182566126009652303041 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP9_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_1_enclosure :
    manuscriptNormP9_1Term ∈ Set.Icc ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_1_rounded_endpoints.1
  have hhi : (manuscriptNormP9_1Interval.2 : ℝ) ≤ ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_1_exact_interval.1, manuscriptNormP9_1_exact_interval.2.trans hhi⟩

def manuscriptNormP9_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP9_2Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP9_2Arg).re

def manuscriptNormP9_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) (-3) (0) (818021 / 781250) (161 / 890)

private theorem manuscriptNormP9_2_arg_eq : manuscriptNormP9_2Arg = barrierComplex (89 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_2_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_2_exact_interval :
    manuscriptNormP9_2Term ∈ Set.Icc (manuscriptNormP9_2Interval.1 : ℝ) (manuscriptNormP9_2Interval.2 : ℝ) := by
  unfold manuscriptNormP9_2Term
  rw [manuscriptNormP9_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-85926283605499 / 8000000000000000) (-53536907546363 / 4000000000000000)
    manuscriptNormP9_2Arg (-3) (0) (818021 / 781250) (89 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (89 / 250) : ℚ) = (161 / 890) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_2_rounded_endpoints :
    (3328926488531865759414963479 / 250000000000000000000000000000) ≤ manuscriptNormP9_2Interval.1 ∧ manuscriptNormP9_2Interval.2 ≤ (1664463244265932879979458429 / 125000000000000000000000000000) := by
  simp only [manuscriptNormP9_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_2_enclosure :
    manuscriptNormP9_2Term ∈ Set.Icc ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((3328926488531865759414963479 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_2_rounded_endpoints.1
  have hhi : (manuscriptNormP9_2Interval.2 : ℝ) ≤ ((1664463244265932879979458429 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_2_exact_interval.1, manuscriptNormP9_2_exact_interval.2.trans hhi⟩

def manuscriptNormP9_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP9_3Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP9_3Arg).re

def manuscriptNormP9_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (150530316475111 / 40000000000000000) (-334867072933799 / 20000000000000000) (1) (0) (16918021 / 12500000) (-161 / 4110)

private theorem manuscriptNormP9_3_arg_eq : manuscriptNormP9_3Arg = barrierComplex (411 / 250) (-161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_3_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (150530316475111 / 40000000000000000) (-334867072933799 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_3_exact_interval :
    manuscriptNormP9_3Term ∈ Set.Icc (manuscriptNormP9_3Interval.1 : ℝ) (manuscriptNormP9_3Interval.2 : ℝ) := by
  unfold manuscriptNormP9_3Term
  rw [manuscriptNormP9_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (150530316475111 / 40000000000000000) (-334867072933799 / 20000000000000000)
    manuscriptNormP9_3Arg (1) (0) (16918021 / 12500000) (411 / 250) (-161 / 2500)
  have hratio : ((-161 / 2500) / (411 / 250) : ℚ) = (-161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_3_rounded_endpoints :
    (1218174183467901772278121067 / 1000000000000000000000000000000) ≤ manuscriptNormP9_3Interval.1 ∧ manuscriptNormP9_3Interval.2 ≤ (121817418346790177253223493 / 100000000000000000000000000000) := by
  simp only [manuscriptNormP9_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_3_enclosure :
    manuscriptNormP9_3Term ∈ Set.Icc ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((1218174183467901772278121067 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_3_rounded_endpoints.1
  have hhi : (manuscriptNormP9_3Interval.2 : ℝ) ≤ ((121817418346790177253223493 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_3_exact_interval.1, manuscriptNormP9_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
