import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP8_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP8_5Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP8_5Arg).re

def manuscriptNormP8_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP8_5_arg_eq : manuscriptNormP8_5Arg = barrierComplex (109 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_5_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_5_exact_interval :
    manuscriptNormP8_5Term ∈ Set.Icc (manuscriptNormP8_5Interval.1 : ℝ) (manuscriptNormP8_5Interval.2 : ℝ) := by
  unfold manuscriptNormP8_5Term
  rw [manuscriptNormP8_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000)
    manuscriptNormP8_5Arg (-5) (-1) (1340981 / 781250) (1481 / 5000) (699 / 5000)
  have hratio : ((699 / 5000) / (1481 / 5000) : ℚ) = (699 / 1481) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_5_rounded_endpoints :
    (-1695532107765573608087953091 / 1000000000000000000000000000000) ≤ manuscriptNormP8_5Interval.1 ∧ manuscriptNormP8_5Interval.2 ≤ (-1695532107765573584766603021 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP8_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_5_enclosure :
    manuscriptNormP8_5Term ∈ Set.Icc ((-1695532107765573608087953091 / 1000000000000000000000000000000) : ℝ) ((-1695532107765573584766603021 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1695532107765573608087953091 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_5_rounded_endpoints.1
  have hhi : (manuscriptNormP8_5Interval.2 : ℝ) ≤ ((-1695532107765573584766603021 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_5_exact_interval.1, manuscriptNormP8_5_exact_interval.2.trans hhi⟩

def manuscriptNormP8_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP8_6Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP8_6Arg).re

def manuscriptNormP8_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP8_6_arg_eq : manuscriptNormP8_6Arg = barrierComplex (115929 / 62500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_6_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_6_exact_interval :
    manuscriptNormP8_6Term ∈ Set.Icc (manuscriptNormP8_6Interval.1 : ℝ) (manuscriptNormP8_6Interval.2 : ℝ) := by
  unfold manuscriptNormP8_6Term
  rw [manuscriptNormP8_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-43980712089603 / 20000000000000000) (5264514136521 / 20000000000000000)
    manuscriptNormP8_6Arg (1) (0) (13439533041 / 7812500000) (115929 / 62500) (0 / 1)
  have hratio : ((0 / 1) / (115929 / 62500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_6_rounded_endpoints :
    (-679294608546064296957873481 / 500000000000000000000000000000) ≤ manuscriptNormP8_6Interval.1 ∧ manuscriptNormP8_6Interval.2 ≤ (-271717843418425718753445767 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP8_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_6_enclosure :
    manuscriptNormP8_6Term ∈ Set.Icc ((-679294608546064296957873481 / 500000000000000000000000000000) : ℝ) ((-271717843418425718753445767 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-679294608546064296957873481 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_6_rounded_endpoints.1
  have hhi : (manuscriptNormP8_6Interval.2 : ℝ) ≤ ((-271717843418425718753445767 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_6_exact_interval.1, manuscriptNormP8_6_exact_interval.2.trans hhi⟩

def manuscriptNormP8_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP8_7Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP8_7Arg).re

def manuscriptNormP8_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709)

private theorem manuscriptNormP8_7_arg_eq : manuscriptNormP8_7Arg = barrierComplex (10129 / 62500) (-529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_7_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_7_exact_interval :
    manuscriptNormP8_7Term ∈ Set.Icc (manuscriptNormP8_7Interval.1 : ℝ) (manuscriptNormP8_7Interval.2 : ℝ) := by
  unfold manuscriptNormP8_7Term
  rw [manuscriptNormP8_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000)
    manuscriptNormP8_7Arg (-5) (-1) (429066082 / 244140625) (20709 / 62500) (-451 / 62500)
  have hratio : ((-451 / 62500) / (20709 / 62500) : ℚ) = (-451 / 20709) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_7_rounded_endpoints :
    (-1726739613144089201383812039 / 1000000000000000000000000000000) ≤ manuscriptNormP8_7Interval.1 ∧ manuscriptNormP8_7Interval.2 ≤ (-345347922628817831427739889 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP8_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_7_enclosure :
    manuscriptNormP8_7Term ∈ Set.Icc ((-1726739613144089201383812039 / 1000000000000000000000000000000) : ℝ) ((-345347922628817831427739889 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-1726739613144089201383812039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_7_rounded_endpoints.1
  have hhi : (manuscriptNormP8_7Interval.2 : ℝ) ≤ ((-345347922628817831427739889 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_7_exact_interval.1, manuscriptNormP8_7_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
