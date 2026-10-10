import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP8_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP8_8Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP8_8Arg).re

def manuscriptNormP8_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871)

private theorem manuscriptNormP8_8_arg_eq : manuscriptNormP8_8Arg = barrierComplex (114871 / 62500) (529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_8_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (78218217469073 / 40000000000000000) (299094251013 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_8_exact_interval :
    manuscriptNormP8_8Term ∈ Set.Icc (manuscriptNormP8_8Interval.1 : ℝ) (manuscriptNormP8_8Interval.2 : ℝ) := by
  unfold manuscriptNormP8_8Term
  rw [manuscriptNormP8_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (78218217469073 / 40000000000000000) (299094251013 / 312500000000000)
    manuscriptNormP8_8Arg (1) (0) (13307283041 / 7812500000) (114871 / 62500) (529 / 3125)
  have hratio : ((529 / 3125) / (114871 / 62500) : ℚ) = (10580 / 114871) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_8_rounded_endpoints :
    (27763238406284779542406107 / 25000000000000000000000000000) ≤ manuscriptNormP8_8Interval.1 ∧ manuscriptNormP8_8Interval.2 ≤ (1110529536251391181828299469 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP8_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_8_enclosure :
    manuscriptNormP8_8Term ∈ Set.Icc ((27763238406284779542406107 / 25000000000000000000000000000) : ℝ) ((1110529536251391181828299469 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((27763238406284779542406107 / 25000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_8_rounded_endpoints.1
  have hhi : (manuscriptNormP8_8Interval.2 : ℝ) ≤ ((1110529536251391181828299469 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_8_exact_interval.1, manuscriptNormP8_8_exact_interval.2.trans hhi⟩

def manuscriptNormP8_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP8_9Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP8_9Arg).re

def manuscriptNormP8_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP8_9_arg_eq : manuscriptNormP8_9Arg = barrierComplex (9071 / 62500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_9_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-17416956232733 / 8000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_9_exact_interval :
    manuscriptNormP8_9Term ∈ Set.Icc (manuscriptNormP8_9Interval.1 : ℝ) (manuscriptNormP8_9Interval.2 : ℝ) := by
  unfold manuscriptNormP8_9Term
  rw [manuscriptNormP8_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-17416956232733 / 8000000000000000) (0 / 1)
    manuscriptNormP8_9Arg (-6) (0) (329132164 / 244140625) (9071 / 62500) (0 / 1)
  have hratio : ((0 / 1) / (9071 / 62500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_9_rounded_endpoints :
    (1050505916849039857336730669 / 250000000000000000000000000000) ≤ manuscriptNormP8_9Interval.1 ∧ manuscriptNormP8_9Interval.2 ≤ (4202023667396159430228982209 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP8_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_9_enclosure :
    manuscriptNormP8_9Term ∈ Set.Icc ((1050505916849039857336730669 / 250000000000000000000000000000) : ℝ) ((4202023667396159430228982209 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1050505916849039857336730669 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_9_rounded_endpoints.1
  have hhi : (manuscriptNormP8_9Interval.2 : ℝ) ≤ ((4202023667396159430228982209 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_9_exact_interval.1, manuscriptNormP8_9_exact_interval.2.trans hhi⟩

def manuscriptNormP9_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP9_0Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP9_0Arg).re

def manuscriptNormP9_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301)

private theorem manuscriptNormP9_0_arg_eq : manuscriptNormP9_0Arg = barrierComplex (5391 / 5000) (391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_0_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_0_exact_interval :
    manuscriptNormP9_0Term ∈ Set.Icc (manuscriptNormP9_0Interval.1 : ℝ) (manuscriptNormP9_0Interval.2 : ℝ) := by
  unfold manuscriptNormP9_0Term
  rw [manuscriptNormP9_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000)
    manuscriptNormP9_0Arg (0) (1) (44350981 / 25000000) (9301 / 5000) (-1481 / 5000)
  have hratio : ((-1481 / 5000) / (9301 / 5000) : ℚ) = (-1481 / 9301) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_0_rounded_endpoints :
    (1190936412496125239808027647 / 500000000000000000000000000000) ≤ manuscriptNormP9_0Interval.1 ∧ manuscriptNormP9_0Interval.2 ≤ (476374564998450126700803411 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP9_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_0_enclosure :
    manuscriptNormP9_0Term ∈ Set.Icc ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_0_rounded_endpoints.1
  have hhi : (manuscriptNormP9_0Interval.2 : ℝ) ≤ ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_0_exact_interval.1, manuscriptNormP9_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
