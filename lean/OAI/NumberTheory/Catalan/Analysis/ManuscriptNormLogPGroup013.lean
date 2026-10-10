import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP4_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP4_0Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP4_0Arg).re

def manuscriptNormP4_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) (0) (-1) (243521 / 160000) (111 / 689)

private theorem manuscriptNormP4_0_arg_eq : manuscriptNormP4_0Arg = barrierComplex (1 / 1) (-289 / 400) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_0_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_0_exact_interval :
    manuscriptNormP4_0Term ∈ Set.Icc (manuscriptNormP4_0Interval.1 : ℝ) (manuscriptNormP4_0Interval.2 : ℝ) := by
  unfold manuscriptNormP4_0Term
  rw [manuscriptNormP4_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2875428436063 / 5000000000000000) (-2802770610277 / 1000000000000000)
    manuscriptNormP4_0Arg (0) (-1) (243521 / 160000) (689 / 400) (111 / 400)
  have hratio : ((111 / 400) / (689 / 400) : ℚ) = (111 / 689) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_0_rounded_endpoints :
    (-1874379120731079543064084237 / 1000000000000000000000000000000) ≤ manuscriptNormP4_0Interval.1 ∧ manuscriptNormP4_0Interval.2 ≤ (-117148695045692465091096139 / 62500000000000000000000000000) := by
  simp only [manuscriptNormP4_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_0_enclosure :
    manuscriptNormP4_0Term ∈ Set.Icc ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
  have hlo : ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_0_rounded_endpoints.1
  have hhi : (manuscriptNormP4_0Interval.2 : ℝ) ≤ ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_0_exact_interval.1, manuscriptNormP4_0_exact_interval.2.trans hhi⟩

def manuscriptNormP4_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP4_1Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP4_1Arg).re

def manuscriptNormP4_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) (0) (-1) (1638401 / 1000000) (201 / 1799)

private theorem manuscriptNormP4_1_arg_eq : manuscriptNormP4_1Arg = barrierComplex (1 / 1) (-799 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_1_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_1_exact_interval :
    manuscriptNormP4_1Term ∈ Set.Icc (manuscriptNormP4_1Interval.1 : ℝ) (manuscriptNormP4_1Interval.2 : ℝ) := by
  unfold manuscriptNormP4_1Term
  rw [manuscriptNormP4_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2637591701359 / 20000000000000000) (-2570943658261 / 4000000000000000)
    manuscriptNormP4_1Arg (0) (-1) (1638401 / 1000000) (1799 / 1000) (201 / 1000)
  have hratio : ((201 / 1000) / (1799 / 1000) : ℚ) = (201 / 1799) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_1_rounded_endpoints :
    (-465843978124225478021104641 / 1000000000000000000000000000000) ≤ manuscriptNormP4_1Interval.1 ∧ manuscriptNormP4_1Interval.2 ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP4_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_1_enclosure :
    manuscriptNormP4_1Term ∈ Set.Icc ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_1_rounded_endpoints.1
  have hhi : (manuscriptNormP4_1Interval.2 : ℝ) ≤ ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_1_exact_interval.1, manuscriptNormP4_1_exact_interval.2.trans hhi⟩

def manuscriptNormP4_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP4_2Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP4_2Arg).re

def manuscriptNormP4_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP4_2_arg_eq : manuscriptNormP4_2Arg = barrierComplex (319 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_2_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_2_exact_interval :
    manuscriptNormP4_2Term ∈ Set.Icc (manuscriptNormP4_2Interval.1 : ℝ) (manuscriptNormP4_2Interval.2 : ℝ) := by
  unfold manuscriptNormP4_2Term
  rw [manuscriptNormP4_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000)
    manuscriptNormP4_2Arg (1) (0) (101761 / 80000) (319 / 200) (0 / 1)
  have hratio : ((0 / 1) / (319 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_2_rounded_endpoints :
    (-127531733280728920730965549 / 40000000000000000000000000000) ≤ manuscriptNormP4_2Interval.1 ∧ manuscriptNormP4_2Interval.2 ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP4_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_2_enclosure :
    manuscriptNormP4_2Term ∈ Set.Icc ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_2_rounded_endpoints.1
  have hhi : (manuscriptNormP4_2Interval.2 : ℝ) ≤ ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_2_exact_interval.1, manuscriptNormP4_2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
