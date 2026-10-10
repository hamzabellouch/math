import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP1_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP1_3Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP1_3Arg).re

def manuscriptNormP1_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) (0) (1) (358241 / 250000) (-171 / 829)

private theorem manuscriptNormP1_3_arg_eq : manuscriptNormP1_3Arg = barrierComplex (1 / 1) (329 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_3_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_3_exact_interval :
    manuscriptNormP1_3Term ∈ Set.Icc (manuscriptNormP1_3Interval.1 : ℝ) (manuscriptNormP1_3Interval.2 : ℝ) := by
  unfold manuscriptNormP1_3Term
  rw [manuscriptNormP1_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70967383232149 / 10000000000000000) (-68330346181621 / 20000000000000000)
    manuscriptNormP1_3Arg (0) (1) (358241 / 250000) (829 / 500) (-171 / 500)
  have hratio : ((-171 / 500) / (829 / 500) : ℚ) = (-171 / 829) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_3_rounded_endpoints :
    (355915867220082359324675621 / 500000000000000000000000000000) ≤ manuscriptNormP1_3Interval.1 ∧ manuscriptNormP1_3Interval.2 ≤ (711831734440164842505553349 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_3_enclosure :
    manuscriptNormP1_3Term ∈ Set.Icc ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((355915867220082359324675621 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_3_rounded_endpoints.1
  have hhi : (manuscriptNormP1_3Interval.2 : ℝ) ≤ ((711831734440164842505553349 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_3_exact_interval.1, manuscriptNormP1_3_exact_interval.2.trans hhi⟩

def manuscriptNormP1_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP1_4Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP1_4Arg).re

def manuscriptNormP1_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799)

private theorem manuscriptNormP1_4_arg_eq : manuscriptNormP1_4Arg = barrierComplex (1 / 1) (-799 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_4_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_4_exact_interval :
    manuscriptNormP1_4Term ∈ Set.Icc (manuscriptNormP1_4Interval.1 : ℝ) (manuscriptNormP1_4Interval.2 : ℝ) := by
  unfold manuscriptNormP1_4Term
  rw [manuscriptNormP1_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000)
    manuscriptNormP1_4Arg (0) (-1) (1638401 / 1000000) (1799 / 1000) (201 / 1000)
  have hratio : ((201 / 1000) / (1799 / 1000) : ℚ) = (201 / 1799) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_4_rounded_endpoints :
    (-465843978124225478021104641 / 1000000000000000000000000000000) ≤ manuscriptNormP1_4Interval.1 ∧ manuscriptNormP1_4Interval.2 ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_4_enclosure :
    manuscriptNormP1_4Term ∈ Set.Icc ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_4_rounded_endpoints.1
  have hhi : (manuscriptNormP1_4Interval.2 : ℝ) ≤ ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_4_exact_interval.1, manuscriptNormP1_4_exact_interval.2.trans hhi⟩

def manuscriptNormP1_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 1 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP1_5Term : ℝ :=
  (-((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP1_5Arg).re

def manuscriptNormP1_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799)

private theorem manuscriptNormP1_5_arg_eq : manuscriptNormP1_5Arg = barrierComplex (1 / 1) (799 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP1_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP1_5_weight_eq :
    -((barrierP2Tail.getD 1 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP1_5_exact_interval :
    manuscriptNormP1_5Term ∈ Set.Icc (manuscriptNormP1_5Interval.1 : ℝ) (manuscriptNormP1_5Interval.2 : ℝ) := by
  unfold manuscriptNormP1_5Term
  rw [manuscriptNormP1_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000)
    manuscriptNormP1_5Arg (0) (1) (1638401 / 1000000) (1799 / 1000) (-201 / 1000)
  have hratio : ((-201 / 1000) / (1799 / 1000) : ℚ) = (-201 / 1799) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP1_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP1_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP1_5_rounded_endpoints :
    (-465843978124225478021104641 / 1000000000000000000000000000000) ≤ manuscriptNormP1_5Interval.1 ∧ manuscriptNormP1_5Interval.2 ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP1_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP1_5_enclosure :
    manuscriptNormP1_5Term ∈ Set.Icc ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP1_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_5_rounded_endpoints.1
  have hhi : (manuscriptNormP1_5Interval.2 : ℝ) ≤ ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP1_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP1_5_exact_interval.1, manuscriptNormP1_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
