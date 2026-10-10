import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP7_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP7_9Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP7_9Arg).re

def manuscriptNormP7_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-43980712089603 / 20000000000000000) (-5264514136521 / 20000000000000000) (1) (0) (13439533041 / 7812500000) (0 / 1)

private theorem manuscriptNormP7_9_arg_eq : manuscriptNormP7_9Arg = barrierComplex (115929 / 62500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_9_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-43980712089603 / 20000000000000000) (-5264514136521 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_9_exact_interval :
    manuscriptNormP7_9Term ∈ Set.Icc (manuscriptNormP7_9Interval.1 : ℝ) (manuscriptNormP7_9Interval.2 : ℝ) := by
  unfold manuscriptNormP7_9Term
  rw [manuscriptNormP7_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-43980712089603 / 20000000000000000) (-5264514136521 / 20000000000000000)
    manuscriptNormP7_9Arg (1) (0) (13439533041 / 7812500000) (115929 / 62500) (0 / 1)
  have hratio : ((0 / 1) / (115929 / 62500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_9_rounded_endpoints :
    (-679294608546064296957873481 / 500000000000000000000000000000) ≤ manuscriptNormP7_9Interval.1 ∧ manuscriptNormP7_9Interval.2 ≤ (-271717843418425718753445767 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP7_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_9_enclosure :
    manuscriptNormP7_9Term ∈ Set.Icc ((-679294608546064296957873481 / 500000000000000000000000000000) : ℝ) ((-271717843418425718753445767 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-679294608546064296957873481 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_9_rounded_endpoints.1
  have hhi : (manuscriptNormP7_9Interval.2 : ℝ) ≤ ((-271717843418425718753445767 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_9_exact_interval.1, manuscriptNormP7_9_exact_interval.2.trans hhi⟩

def manuscriptNormP8_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP8_0Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP8_0Arg).re

def manuscriptNormP8_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301)

private theorem manuscriptNormP8_0_arg_eq : manuscriptNormP8_0Arg = barrierComplex (5391 / 5000) (-391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_0_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_0_exact_interval :
    manuscriptNormP8_0Term ∈ Set.Icc (manuscriptNormP8_0Interval.1 : ℝ) (manuscriptNormP8_0Interval.2 : ℝ) := by
  unfold manuscriptNormP8_0Term
  rw [manuscriptNormP8_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000)
    manuscriptNormP8_0Arg (0) (-1) (44350981 / 25000000) (9301 / 5000) (1481 / 5000)
  have hratio : ((1481 / 5000) / (9301 / 5000) : ℚ) = (1481 / 9301) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_0_rounded_endpoints :
    (1190936412496125239808027647 / 500000000000000000000000000000) ≤ manuscriptNormP8_0Interval.1 ∧ manuscriptNormP8_0Interval.2 ≤ (476374564998450126700803411 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP8_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_0_enclosure :
    manuscriptNormP8_0Term ∈ Set.Icc ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_0_rounded_endpoints.1
  have hhi : (manuscriptNormP8_0Interval.2 : ℝ) ≤ ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_0_exact_interval.1, manuscriptNormP8_0_exact_interval.2.trans hhi⟩

def manuscriptNormP8_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 8 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP8_1Term : ℝ :=
  (-((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP8_1Arg).re

def manuscriptNormP8_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) (0) (-1) (301299661 / 156250000) (2771 / 24391)

private theorem manuscriptNormP8_1_arg_eq : manuscriptNormP8_1Arg = barrierComplex (13581 / 12500) (-1081 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormP8_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP8_1_weight_eq :
    -((barrierP2Tail.getD 8 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP8_1_exact_interval :
    manuscriptNormP8_1Term ∈ Set.Icc (manuscriptNormP8_1Interval.1 : ℝ) (manuscriptNormP8_1Interval.2 : ℝ) := by
  unfold manuscriptNormP8_1Term
  rw [manuscriptNormP8_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-70453504591 / 312500000000000) (19469072932083 / 20000000000000000)
    manuscriptNormP8_1Arg (0) (-1) (301299661 / 156250000) (24391 / 12500) (2771 / 12500)
  have hratio : ((2771 / 12500) / (24391 / 12500) : ℚ) = (2771 / 24391) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP8_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP8_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP8_1_rounded_endpoints :
    (29020409128306298718006873 / 50000000000000000000000000000) ≤ manuscriptNormP8_1Interval.1 ∧ manuscriptNormP8_1Interval.2 ≤ (580408182566126009652303041 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP8_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP8_1_enclosure :
    manuscriptNormP8_1Term ∈ Set.Icc ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((29020409128306298718006873 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP8_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_1_rounded_endpoints.1
  have hhi : (manuscriptNormP8_1Interval.2 : ℝ) ≤ ((580408182566126009652303041 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP8_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP8_1_exact_interval.1, manuscriptNormP8_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
