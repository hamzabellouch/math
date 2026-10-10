import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP1_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP1_0Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP1_0Arg).re

def manuscriptNormP1_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4999594751017 / 2500000000000000) (0 / 1) (-5) (0) (40401 / 31250) (0 / 1)

private theorem manuscriptNormP1_0_arg_eq : manuscriptNormP1_0Arg = barrierComplex (201 / 1000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_0_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-4999594751017 / 2500000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_0_exact_interval :
    manuscriptNormP1_0Term ∈ Set.Icc (manuscriptNormP1_0Interval.1 : ℝ) (manuscriptNormP1_0Interval.2 : ℝ) := by
  unfold manuscriptNormP1_0Term
  rw [manuscriptNormP1_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4999594751017 / 2500000000000000) (0 / 1)
    manuscriptNormP1_0Arg (-5) (0) (40401 / 31250) (201 / 1000) (0 / 1)
  have hratio : ((0 / 1) / (201 / 1000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_0_rounded_endpoints :
    (3208640661093686383961006697 / 1000000000000000000000000000000) ≤ manuscriptNormP1_0Interval.1 ∧ manuscriptNormP1_0Interval.2 ≤ (3208640661093686384636201629 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_0_enclosure :
    manuscriptNormP1_0Term ∈ Set.Icc ((3208640661093686383961006697 / 1000000000000000000000000000000) : ℝ) ((3208640661093686384636201629 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((3208640661093686383961006697 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_0_rounded_endpoints.1
  have hhi : (manuscriptNormP1_0Interval.2 : ℝ) ≤ ((3208640661093686384636201629 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_0_exact_interval.1, manuscriptNormP1_0_exact_interval.2.trans hhi⟩

def manuscriptNormP1_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP1_1Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP1_1Arg).re

def manuscriptNormP1_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-4586060797081 / 10000000000000000) (0 / 1) (-7) (0) (677448 / 390625) (0 / 1)

private theorem manuscriptNormP1_1_arg_eq : manuscriptNormP1_1Arg = barrierComplex (291 / 2500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_1_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-4586060797081 / 10000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_1_exact_interval :
    manuscriptNormP1_1Term ∈ Set.Icc (manuscriptNormP1_1Interval.1 : ℝ) (manuscriptNormP1_1Interval.2 : ℝ) := by
  unfold manuscriptNormP1_1Term
  rw [manuscriptNormP1_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-4586060797081 / 10000000000000000) (0 / 1)
    manuscriptNormP1_1Arg (-7) (0) (677448 / 390625) (291 / 2500) (0 / 1)
  have hratio : ((0 / 1) / (291 / 2500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_1_rounded_endpoints :
    (986334526020334732753129213 / 1000000000000000000000000000000) ≤ manuscriptNormP1_1Interval.1 ∧ manuscriptNormP1_1Interval.2 ≤ (246583631505083683242477679 / 250000000000000000000000000000) := by
  simp only [manuscriptNormP1_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_1_enclosure :
    manuscriptNormP1_1Term ∈ Set.Icc ((986334526020334732753129213 / 1000000000000000000000000000000) : ℝ) ((246583631505083683242477679 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((986334526020334732753129213 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_1_rounded_endpoints.1
  have hhi : (manuscriptNormP1_1Interval.2 : ℝ) ≤ ((246583631505083683242477679 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_1_exact_interval.1, manuscriptNormP1_1_exact_interval.2.trans hhi⟩

def manuscriptNormP1_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP1_2Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP1_2Arg).re

def manuscriptNormP1_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829)

private theorem manuscriptNormP1_2_arg_eq : manuscriptNormP1_2Arg = barrierComplex (1 / 1) (-329 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_2_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_2_exact_interval :
    manuscriptNormP1_2Term ∈ Set.Icc (manuscriptNormP1_2Interval.1 : ℝ) (manuscriptNormP1_2Interval.2 : ℝ) := by
  unfold manuscriptNormP1_2Term
  rw [manuscriptNormP1_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000)
    manuscriptNormP1_2Arg (0) (-1) (358241 / 250000) (829 / 500) (171 / 500)
  have hratio : ((171 / 500) / (829 / 500) : ℚ) = (171 / 829) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_2_rounded_endpoints :
    (355915867220082359324675621 / 500000000000000000000000000000) ≤ manuscriptNormP1_2Interval.1 ∧ manuscriptNormP1_2Interval.2 ≤ (711831734440164842505553349 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_2_enclosure :
    manuscriptNormP1_2Term ∈ Set.Icc ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_2_rounded_endpoints.1
  have hhi : (manuscriptNormP1_2Interval.2 : ℝ) ≤ ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_2_exact_interval.1, manuscriptNormP1_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
