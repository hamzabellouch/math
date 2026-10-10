import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP0_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP0_4Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP0_4Arg).re

def manuscriptNormP0_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689)

private theorem manuscriptNormP0_4_arg_eq : manuscriptNormP0_4Arg = barrierComplex (1 / 1) (-289 / 400) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_4_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_4_exact_interval :
    manuscriptNormP0_4Term ∈ Set.Icc (manuscriptNormP0_4Interval.1 : ℝ) (manuscriptNormP0_4Interval.2 : ℝ) := by
  unfold manuscriptNormP0_4Term
  rw [manuscriptNormP0_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000)
    manuscriptNormP0_4Arg (0) (-1) (243521 / 160000) (689 / 400) (111 / 400)
  have hratio : ((111 / 400) / (689 / 400) : ℚ) = (111 / 689) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_4_rounded_endpoints :
    (-1874379120731079543064084237 / 1000000000000000000000000000000) ≤ manuscriptNormP0_4Interval.1 ∧ manuscriptNormP0_4Interval.2 ≤ (-117148695045692465091096139 / 62500000000000000000000000000) := by
  simp only [manuscriptNormP0_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_4_enclosure :
    manuscriptNormP0_4Term ∈ Set.Icc ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
  have hlo : ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_4_rounded_endpoints.1
  have hhi : (manuscriptNormP0_4Interval.2 : ℝ) ≤ ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_4_exact_interval.1, manuscriptNormP0_4_exact_interval.2.trans hhi⟩

def manuscriptNormP0_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP0_5Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP0_5Arg).re

def manuscriptNormP0_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689)

private theorem manuscriptNormP0_5_arg_eq : manuscriptNormP0_5Arg = barrierComplex (1 / 1) (289 / 400) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_5_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_5_exact_interval :
    manuscriptNormP0_5Term ∈ Set.Icc (manuscriptNormP0_5Interval.1 : ℝ) (manuscriptNormP0_5Interval.2 : ℝ) := by
  unfold manuscriptNormP0_5Term
  rw [manuscriptNormP0_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000)
    manuscriptNormP0_5Arg (0) (1) (243521 / 160000) (689 / 400) (-111 / 400)
  have hratio : ((-111 / 400) / (689 / 400) : ℚ) = (-111 / 689) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_5_rounded_endpoints :
    (-1874379120731079543064084237 / 1000000000000000000000000000000) ≤ manuscriptNormP0_5Interval.1 ∧ manuscriptNormP0_5Interval.2 ≤ (-117148695045692465091096139 / 62500000000000000000000000000) := by
  simp only [manuscriptNormP0_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_5_enclosure :
    manuscriptNormP0_5Term ∈ Set.Icc ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
  have hlo : ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_5_rounded_endpoints.1
  have hhi : (manuscriptNormP0_5Interval.2 : ℝ) ≤ ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_5_exact_interval.1, manuscriptNormP0_5_exact_interval.2.trans hhi⟩

def manuscriptNormP0_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 0 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP0_6Term : ℝ :=
  (-((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP0_6Arg).re

def manuscriptNormP0_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) (0) (-1) (36530981 / 25000000) (699 / 8519)

private theorem manuscriptNormP0_6_arg_eq : manuscriptNormP0_6Arg = barrierComplex (4609 / 5000) (-391 / 500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP0_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP0_6_weight_eq :
    -((barrierP2Tail.getD 0 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP0_6_exact_interval :
    manuscriptNormP0_6Term ∈ Set.Icc (manuscriptNormP0_6Interval.1 : ℝ) (manuscriptNormP0_6Interval.2 : ℝ) := by
  unfold manuscriptNormP0_6Term
  rw [manuscriptNormP0_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3765635049867 / 2500000000000000) (-10421985581721 / 2500000000000000)
    manuscriptNormP0_6Arg (0) (-1) (36530981 / 25000000) (8519 / 5000) (699 / 5000)
  have hratio : ((699 / 5000) / (8519 / 5000) : ℚ) = (699 / 8519) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP0_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP0_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP0_6_rounded_endpoints :
    (-160926007121511347938212133 / 50000000000000000000000000000) ≤ manuscriptNormP0_6Interval.1 ∧ manuscriptNormP0_6Interval.2 ≤ (-1609260071215113403818180873 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP0_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP0_6_enclosure :
    manuscriptNormP0_6Term ∈ Set.Icc ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-160926007121511347938212133 / 50000000000000000000000000000) : ℝ) ≤ (manuscriptNormP0_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_6_rounded_endpoints.1
  have hhi : (manuscriptNormP0_6Interval.2 : ℝ) ≤ ((-1609260071215113403818180873 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP0_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP0_6_exact_interval.1, manuscriptNormP0_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
