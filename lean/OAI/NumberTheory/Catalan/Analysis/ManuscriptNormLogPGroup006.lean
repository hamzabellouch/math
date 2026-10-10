import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP1_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP1_9Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP1_9Arg).re

def manuscriptNormP1_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) (0) (1) (301299661 / 156250000) (-2771 / 24391)

private theorem manuscriptNormP1_9_arg_eq : manuscriptNormP1_9Arg = barrierComplex (13581 / 12500) (1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_9_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_9_exact_interval :
    manuscriptNormP1_9Term ∈ Set.Icc (manuscriptNormP1_9Interval.1 : ℝ) (manuscriptNormP1_9Interval.2 : ℝ) := by
  unfold manuscriptNormP1_9Term
  rw [manuscriptNormP1_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70453504591 / 312500000000000) (-19469072932083 / 20000000000000000)
    manuscriptNormP1_9Arg (0) (1) (301299661 / 156250000) (24391 / 12500) (-2771 / 12500)
  have hratio : ((-2771 / 12500) / (24391 / 12500) : ℚ) = (-2771 / 24391) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_9_rounded_endpoints :
    (29020409128306298718006873 / 50000000000000000000000000000) ≤ manuscriptNormP1_9Interval.1 ∧ manuscriptNormP1_9Interval.2 ≤ (580408182566126009652303041 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_9_enclosure :
    manuscriptNormP1_9Term ∈ Set.Icc ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_9_rounded_endpoints.1
  have hhi : (manuscriptNormP1_9Interval.2 : ℝ) ≤ ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_9_exact_interval.1, manuscriptNormP1_9_exact_interval.2.trans hhi⟩

def manuscriptNormP2_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP2_0Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP2_0Arg).re

def manuscriptNormP2_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) (0) (-1) (54161 / 40000) (81 / 319)

private theorem manuscriptNormP2_0_arg_eq : manuscriptNormP2_0Arg = barrierComplex (1 / 1) (-119 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_0_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_0_exact_interval :
    manuscriptNormP2_0Term ∈ Set.Icc (manuscriptNormP2_0Interval.1 : ℝ) (manuscriptNormP2_0Interval.2 : ℝ) := by
  unfold manuscriptNormP2_0Term
  rw [manuscriptNormP2_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-77366649157093 / 2500000000000000) (74491825385797 / 5000000000000000)
    manuscriptNormP2_0Arg (0) (-1) (54161 / 40000) (319 / 200) (81 / 200)
  have hratio : ((81 / 200) / (319 / 200) : ℚ) = (81 / 319) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_0_rounded_endpoints :
    (661358122763075158075038643 / 200000000000000000000000000000) ≤ manuscriptNormP2_0Interval.1 ∧ manuscriptNormP2_0Interval.2 ≤ (826697653453844082618353217 / 250000000000000000000000000000) := by
  simp only [manuscriptNormP2_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_0_enclosure :
    manuscriptNormP2_0Term ∈ Set.Icc ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((661358122763075158075038643 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_0_rounded_endpoints.1
  have hhi : (manuscriptNormP2_0Interval.2 : ℝ) ≤ ((826697653453844082618353217 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_0_exact_interval.1, manuscriptNormP2_0_exact_interval.2.trans hhi⟩

def manuscriptNormP2_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP2_1Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP2_1Arg).re

def manuscriptNormP2_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) (0) (-1) (358241 / 250000) (171 / 829)

private theorem manuscriptNormP2_1_arg_eq : manuscriptNormP2_1Arg = barrierComplex (1 / 1) (-329 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_1_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_1_exact_interval :
    manuscriptNormP2_1Term ∈ Set.Icc (manuscriptNormP2_1Interval.1 : ℝ) (manuscriptNormP2_1Interval.2 : ℝ) := by
  unfold manuscriptNormP2_1Term
  rw [manuscriptNormP2_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70967383232149 / 10000000000000000) (68330346181621 / 20000000000000000)
    manuscriptNormP2_1Arg (0) (-1) (358241 / 250000) (829 / 500) (171 / 500)
  have hratio : ((171 / 500) / (829 / 500) : ℚ) = (171 / 829) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_1_rounded_endpoints :
    (355915867220082359324675621 / 500000000000000000000000000000) ≤ manuscriptNormP2_1Interval.1 ∧ manuscriptNormP2_1Interval.2 ≤ (711831734440164842505553349 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP2_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_1_enclosure :
    manuscriptNormP2_1Term ∈ Set.Icc ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_1_rounded_endpoints.1
  have hhi : (manuscriptNormP2_1Interval.2 : ℝ) ≤ ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_1_exact_interval.1, manuscriptNormP2_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
