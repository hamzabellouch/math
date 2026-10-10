import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP5_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP5_8Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP5_8Arg).re

def manuscriptNormP5_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP5_8_arg_eq : manuscriptNormP5_8Arg = barrierComplex (109 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_8_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_8_exact_interval :
    manuscriptNormP5_8Term ∈ Set.Icc (manuscriptNormP5_8Interval.1 : ℝ) (manuscriptNormP5_8Interval.2 : ℝ) := by
  unfold manuscriptNormP5_8Term
  rw [manuscriptNormP5_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (51978482934179 / 40000000000000000) (23836077867557 / 40000000000000000)
    manuscriptNormP5_8Arg (-5) (-1) (1340981 / 781250) (1481 / 5000) (699 / 5000)
  have hratio : ((699 / 5000) / (1481 / 5000) : ℚ) = (699 / 1481) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_8_rounded_endpoints :
    (-1695532107765573608087953091 / 1000000000000000000000000000000) ≤ manuscriptNormP5_8Interval.1 ∧ manuscriptNormP5_8Interval.2 ≤ (-1695532107765573584766603021 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP5_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_8_enclosure :
    manuscriptNormP5_8Term ∈ Set.Icc ((-1695532107765573608087953091 / 1000000000000000000000000000000) : ℝ) ((-1695532107765573584766603021 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1695532107765573608087953091 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_8_rounded_endpoints.1
  have hhi : (manuscriptNormP5_8Interval.2 : ℝ) ≤ ((-1695532107765573584766603021 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_8_exact_interval.1, manuscriptNormP5_8_exact_interval.2.trans hhi⟩

def manuscriptNormP5_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP5_9Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP5_9Arg).re

def manuscriptNormP5_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP5_9_arg_eq : manuscriptNormP5_9Arg = barrierComplex (891 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_9_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_9_exact_interval :
    manuscriptNormP5_9Term ∈ Set.Icc (manuscriptNormP5_9Interval.1 : ℝ) (manuscriptNormP5_9Interval.2 : ℝ) := by
  unfold manuscriptNormP5_9Term
  rw [manuscriptNormP5_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000)
    manuscriptNormP5_9Arg (1) (0) (79540981 / 50000000) (891 / 500) (-391 / 5000)
  have hratio : ((-391 / 5000) / (891 / 500) : ℚ) = (-391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_9_rounded_endpoints :
    (-825452530567521026167866743 / 1000000000000000000000000000000) ≤ manuscriptNormP5_9Interval.1 ∧ manuscriptNormP5_9Interval.2 ≤ (-412726265283760513035682481 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP5_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_9_enclosure :
    manuscriptNormP5_9Term ∈ Set.Icc ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_9_rounded_endpoints.1
  have hhi : (manuscriptNormP5_9Interval.2 : ℝ) ≤ ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_9_exact_interval.1, manuscriptNormP5_9_exact_interval.2.trans hhi⟩

def manuscriptNormP6_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 6 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP6_0Term : ℝ :=
  (-((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP6_0Arg).re

def manuscriptNormP6_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519)

private theorem manuscriptNormP6_0_arg_eq : manuscriptNormP6_0Arg = barrierComplex (4609 / 5000) (-391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP6_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP6_0_weight_eq :
    -((barrierP2Tail.getD 6 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP6_0_exact_interval :
    manuscriptNormP6_0Term ∈ Set.Icc (manuscriptNormP6_0Interval.1 : ℝ) (manuscriptNormP6_0Interval.2 : ℝ) := by
  unfold manuscriptNormP6_0Term
  rw [manuscriptNormP6_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000)
    manuscriptNormP6_0Arg (0) (-1) (36530981 / 25000000) (8519 / 5000) (699 / 5000)
  have hratio : ((699 / 5000) / (8519 / 5000) : ℚ) = (699 / 8519) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP6_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP6_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP6_0_rounded_endpoints :
    (-160926007121511347938212133 / 50000000000000000000000000000) ≤ manuscriptNormP6_0Interval.1 ∧ manuscriptNormP6_0Interval.2 ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP6_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP6_0_enclosure :
    manuscriptNormP6_0Term ∈ Set.Icc ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP6_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_0_rounded_endpoints.1
  have hhi : (manuscriptNormP6_0Interval.2 : ℝ) ≤ ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP6_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP6_0_exact_interval.1, manuscriptNormP6_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
