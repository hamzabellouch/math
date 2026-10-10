import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP3_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP3_1Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP3_1Arg).re

def manuscriptNormP3_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829)

private theorem manuscriptNormP3_1_arg_eq : manuscriptNormP3_1Arg = barrierComplex (1 / 1) (329 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_1_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_1_exact_interval :
    manuscriptNormP3_1Term ∈ Set.Icc (manuscriptNormP3_1Interval.1 : ℝ) (manuscriptNormP3_1Interval.2 : ℝ) := by
  unfold manuscriptNormP3_1Term
  rw [manuscriptNormP3_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000)
    manuscriptNormP3_1Arg (0) (1) (358241 / 250000) (829 / 500) (-171 / 500)
  have hratio : ((-171 / 500) / (829 / 500) : ℚ) = (-171 / 829) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_1_rounded_endpoints :
    (355915867220082359324675621 / 500000000000000000000000000000) ≤ manuscriptNormP3_1Interval.1 ∧ manuscriptNormP3_1Interval.2 ≤ (711831734440164842505553349 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP3_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_1_enclosure :
    manuscriptNormP3_1Term ∈ Set.Icc ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_1_rounded_endpoints.1
  have hhi : (manuscriptNormP3_1Interval.2 : ℝ) ≤ ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_1_exact_interval.1, manuscriptNormP3_1_exact_interval.2.trans hhi⟩

def manuscriptNormP3_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP3_2Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP3_2Arg).re

def manuscriptNormP3_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1)

private theorem manuscriptNormP3_2_arg_eq : manuscriptNormP3_2Arg = barrierComplex (51 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_2_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-1082171180825569 / 8000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_2_exact_interval :
    manuscriptNormP3_2Term ∈ Set.Icc (manuscriptNormP3_2Interval.1 : ℝ) (manuscriptNormP3_2Interval.2 : ℝ) := by
  unfold manuscriptNormP3_2Term
  rw [manuscriptNormP3_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1082171180825569 / 8000000000000000) (0 / 1)
    manuscriptNormP3_2Arg (-2) (0) (2601 / 2500) (51 / 100) (0 / 1)
  have hratio : ((0 / 1) / (51 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_2_rounded_endpoints :
    (45542129394244653502391507333 / 500000000000000000000000000000) ≤ manuscriptNormP3_2Interval.1 ∧ manuscriptNormP3_2Interval.2 ≤ (91084258788489307023051407697 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP3_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_2_enclosure :
    manuscriptNormP3_2Term ∈ Set.Icc ((45542129394244653502391507333 / 500000000000000000000000000000) : ℝ) ((91084258788489307023051407697 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((45542129394244653502391507333 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_2_rounded_endpoints.1
  have hhi : (manuscriptNormP3_2Interval.2 : ℝ) ≤ ((91084258788489307023051407697 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_2_exact_interval.1, manuscriptNormP3_2_exact_interval.2.trans hhi⟩

def manuscriptNormP3_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 3 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP3_3Term : ℝ :=
  (-((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP3_3Arg).re

def manuscriptNormP3_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3374669985148323 / 40000000000000000) (-1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1)

private theorem manuscriptNormP3_3_arg_eq : manuscriptNormP3_3Arg = barrierComplex (149 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP3_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP3_3_weight_eq :
    -((barrierP2Tail.getD 3 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-3374669985148323 / 40000000000000000) (-1057383684695809 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP3_3_exact_interval :
    manuscriptNormP3_3Term ∈ Set.Icc (manuscriptNormP3_3Interval.1 : ℝ) (manuscriptNormP3_3Interval.2 : ℝ) := by
  unfold manuscriptNormP3_3Term
  rw [manuscriptNormP3_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3374669985148323 / 40000000000000000) (-1057383684695809 / 10000000000000000)
    manuscriptNormP3_3Arg (1) (0) (22201 / 20000) (149 / 100) (0 / 1)
  have hratio : ((0 / 1) / (149 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP3_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP3_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP3_3_rounded_endpoints :
    (-6728689014070180867221453861 / 200000000000000000000000000000) ≤ manuscriptNormP3_3Interval.1 ∧ manuscriptNormP3_3Interval.2 ≤ (-3364344507035090433041040741 / 100000000000000000000000000000) := by
  simp only [manuscriptNormP3_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP3_3_enclosure :
    manuscriptNormP3_3Term ∈ Set.Icc ((-6728689014070180867221453861 / 200000000000000000000000000000) : ℝ) ((-3364344507035090433041040741 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-6728689014070180867221453861 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP3_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_3_rounded_endpoints.1
  have hhi : (manuscriptNormP3_3Interval.2 : ℝ) ≤ ((-3364344507035090433041040741 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP3_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP3_3_exact_interval.1, manuscriptNormP3_3_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
