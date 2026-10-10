import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP9_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP9_7Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP9_7Arg).re

def manuscriptNormP9_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-43980712089603 / 20000000000000000) (-5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP9_7_arg_eq : manuscriptNormP9_7Arg = barrierComplex (115929 / 62500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_7_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-43980712089603 / 20000000000000000) (-5264514136521 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_7_exact_interval :
    manuscriptNormP9_7Term ∈ Set.Icc (manuscriptNormP9_7Interval.1 : ℝ) (manuscriptNormP9_7Interval.2 : ℝ) := by
  unfold manuscriptNormP9_7Term
  rw [manuscriptNormP9_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-43980712089603 / 20000000000000000) (-5264514136521 / 20000000000000000)
    manuscriptNormP9_7Arg (1) (0) (13439533041 / 7812500000) (115929 / 62500) (0 / 1)
  have hratio : ((0 / 1) / (115929 / 62500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_7_rounded_endpoints :
    (-679294608546064296957873481 / 500000000000000000000000000000) ≤ manuscriptNormP9_7Interval.1 ∧ manuscriptNormP9_7Interval.2 ≤ (-271717843418425718753445767 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP9_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_7_enclosure :
    manuscriptNormP9_7Term ∈ Set.Icc ((-679294608546064296957873481 / 500000000000000000000000000000) : ℝ) ((-271717843418425718753445767 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-679294608546064296957873481 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_7_rounded_endpoints.1
  have hhi : (manuscriptNormP9_7Interval.2 : ℝ) ≤ ((-271717843418425718753445767 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_7_exact_interval.1, manuscriptNormP9_7_exact_interval.2.trans hhi⟩

def manuscriptNormP9_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP9_8Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP9_8Arg).re

def manuscriptNormP9_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-17416956232733 / 8000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP9_8_arg_eq : manuscriptNormP9_8Arg = barrierComplex (9071 / 62500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_8_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-17416956232733 / 8000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_8_exact_interval :
    manuscriptNormP9_8Term ∈ Set.Icc (manuscriptNormP9_8Interval.1 : ℝ) (manuscriptNormP9_8Interval.2 : ℝ) := by
  unfold manuscriptNormP9_8Term
  rw [manuscriptNormP9_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-17416956232733 / 8000000000000000) (0 / 1)
    manuscriptNormP9_8Arg (-6) (0) (329132164 / 244140625) (9071 / 62500) (0 / 1)
  have hratio : ((0 / 1) / (9071 / 62500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_8_rounded_endpoints :
    (1050505916849039857336730669 / 250000000000000000000000000000) ≤ manuscriptNormP9_8Interval.1 ∧ manuscriptNormP9_8Interval.2 ≤ (4202023667396159430228982209 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP9_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_8_enclosure :
    manuscriptNormP9_8Term ∈ Set.Icc ((1050505916849039857336730669 / 250000000000000000000000000000) : ℝ) ((4202023667396159430228982209 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((1050505916849039857336730669 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_8_rounded_endpoints.1
  have hhi : (manuscriptNormP9_8Interval.2 : ℝ) ≤ ((4202023667396159430228982209 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_8_exact_interval.1, manuscriptNormP9_8_exact_interval.2.trans hhi⟩

def manuscriptNormP9_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP9_9Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP9_9Arg).re

def manuscriptNormP9_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (78218217469073 / 40000000000000000) (-299094251013 / 312500000000000) (1) (0) (13307283041 / 7812500000) (-10580 / 114871)

private theorem manuscriptNormP9_9_arg_eq : manuscriptNormP9_9Arg = barrierComplex (114871 / 62500) (-529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_9_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (78218217469073 / 40000000000000000) (-299094251013 / 312500000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_9_exact_interval :
    manuscriptNormP9_9Term ∈ Set.Icc (manuscriptNormP9_9Interval.1 : ℝ) (manuscriptNormP9_9Interval.2 : ℝ) := by
  unfold manuscriptNormP9_9Term
  rw [manuscriptNormP9_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (78218217469073 / 40000000000000000) (-299094251013 / 312500000000000)
    manuscriptNormP9_9Arg (1) (0) (13307283041 / 7812500000) (114871 / 62500) (-529 / 3125)
  have hratio : ((-529 / 3125) / (114871 / 62500) : ℚ) = (-10580 / 114871) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_9_rounded_endpoints :
    (27763238406284779542406107 / 25000000000000000000000000000) ≤ manuscriptNormP9_9Interval.1 ∧ manuscriptNormP9_9Interval.2 ≤ (1110529536251391181828299469 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP9_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_9_enclosure :
    manuscriptNormP9_9Term ∈ Set.Icc ((27763238406284779542406107 / 25000000000000000000000000000) : ℝ) ((1110529536251391181828299469 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((27763238406284779542406107 / 25000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_9_rounded_endpoints.1
  have hhi : (manuscriptNormP9_9Interval.2 : ℝ) ≤ ((1110529536251391181828299469 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_9_exact_interval.1, manuscriptNormP9_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
