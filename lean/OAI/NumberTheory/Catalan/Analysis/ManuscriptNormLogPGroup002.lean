import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP0_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP0_7Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP0_7Arg).re

def manuscriptNormP0_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) (0) (1) (36530981 / 25000000) (-699 / 8519)

private theorem manuscriptNormP0_7_arg_eq : manuscriptNormP0_7Arg = barrierComplex (4609 / 5000) (391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_7_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_7_exact_interval :
    manuscriptNormP0_7Term ∈ Set.Icc (manuscriptNormP0_7Interval.1 : ℝ) (manuscriptNormP0_7Interval.2 : ℝ) := by
  unfold manuscriptNormP0_7Term
  rw [manuscriptNormP0_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3765635049867 / 2500000000000000) (10421985581721 / 2500000000000000)
    manuscriptNormP0_7Arg (0) (1) (36530981 / 25000000) (8519 / 5000) (-699 / 5000)
  have hratio : ((-699 / 5000) / (8519 / 5000) : ℚ) = (-699 / 8519) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_7_rounded_endpoints :
    (-160926007121511347938212133 / 50000000000000000000000000000) ≤ manuscriptNormP0_7Interval.1 ∧ manuscriptNormP0_7Interval.2 ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP0_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_7_enclosure :
    manuscriptNormP0_7Term ∈ Set.Icc ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_7_rounded_endpoints.1
  have hhi : (manuscriptNormP0_7Interval.2 : ℝ) ≤ ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_7_exact_interval.1, manuscriptNormP0_7_exact_interval.2.trans hhi⟩

def manuscriptNormP0_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP0_8Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP0_8Arg).re

def manuscriptNormP0_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) (0) (-1) (44350981 / 25000000) (1481 / 9301)

private theorem manuscriptNormP0_8_arg_eq : manuscriptNormP0_8Arg = barrierComplex (5391 / 5000) (-391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_8_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_8_exact_interval :
    manuscriptNormP0_8Term ∈ Set.Icc (manuscriptNormP0_8Interval.1 : ℝ) (manuscriptNormP0_8Interval.2 : ℝ) := by
  unfold manuscriptNormP0_8Term
  rw [manuscriptNormP0_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-76806433087 / 78125000000000) (21224636816931 / 5000000000000000)
    manuscriptNormP0_8Arg (0) (-1) (44350981 / 25000000) (9301 / 5000) (1481 / 5000)
  have hratio : ((1481 / 5000) / (9301 / 5000) : ℚ) = (1481 / 9301) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_8_rounded_endpoints :
    (1190936412496125239808027647 / 500000000000000000000000000000) ≤ manuscriptNormP0_8Interval.1 ∧ manuscriptNormP0_8Interval.2 ≤ (476374564998450126700803411 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP0_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_8_enclosure :
    manuscriptNormP0_8Term ∈ Set.Icc ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_8_rounded_endpoints.1
  have hhi : (manuscriptNormP0_8Interval.2 : ℝ) ≤ ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_8_exact_interval.1, manuscriptNormP0_8_exact_interval.2.trans hhi⟩

def manuscriptNormP0_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP0_9Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP0_9Arg).re

def manuscriptNormP0_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) (0) (1) (44350981 / 25000000) (-1481 / 9301)

private theorem manuscriptNormP0_9_arg_eq : manuscriptNormP0_9Arg = barrierComplex (5391 / 5000) (391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_9_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_9_exact_interval :
    manuscriptNormP0_9Term ∈ Set.Icc (manuscriptNormP0_9Interval.1 : ℝ) (manuscriptNormP0_9Interval.2 : ℝ) := by
  unfold manuscriptNormP0_9Term
  rw [manuscriptNormP0_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-76806433087 / 78125000000000) (-21224636816931 / 5000000000000000)
    manuscriptNormP0_9Arg (0) (1) (44350981 / 25000000) (9301 / 5000) (-1481 / 5000)
  have hratio : ((-1481 / 5000) / (9301 / 5000) : ℚ) = (-1481 / 9301) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_9_rounded_endpoints :
    (1190936412496125239808027647 / 500000000000000000000000000000) ≤ manuscriptNormP0_9Interval.1 ∧ manuscriptNormP0_9Interval.2 ≤ (476374564998450126700803411 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP0_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_9_enclosure :
    manuscriptNormP0_9Term ∈ Set.Icc ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((1190936412496125239808027647 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_9_rounded_endpoints.1
  have hhi : (manuscriptNormP0_9Interval.2 : ℝ) ≤ ((476374564998450126700803411 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_9_exact_interval.1, manuscriptNormP0_9_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
