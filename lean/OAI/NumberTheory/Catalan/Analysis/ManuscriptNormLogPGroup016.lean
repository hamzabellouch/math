import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP4_9Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 9 (0, 0)).1

def manuscriptNormP4_9Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormP4_9Arg).re

def manuscriptNormP4_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP4_9_arg_eq : manuscriptNormP4_9Arg = barrierComplex (109 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_9Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_9_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 9 (0, 0)).2) =
      barrierComplex (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_9_exact_interval :
    manuscriptNormP4_9Term ∈ Set.Icc (manuscriptNormP4_9Interval.1 : ℝ) (manuscriptNormP4_9Interval.2 : ℝ) := by
  unfold manuscriptNormP4_9Term
  rw [manuscriptNormP4_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000)
    manuscriptNormP4_9Arg (-5) (0) (1340981 / 781250) (109 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (109 / 500) : ℚ) = (391 / 1090) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_9Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_9_rounded_endpoints :
    (-339106421553114718088507527 / 200000000000000000000000000000) ≤ manuscriptNormP4_9Interval.1 ∧ manuscriptNormP4_9Interval.2 ≤ (-21194151347069669875047383 / 12500000000000000000000000000) := by
  simp only [manuscriptNormP4_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_9_enclosure :
    manuscriptNormP4_9Term ∈ Set.Icc ((-339106421553114718088507527 / 200000000000000000000000000000) : ℝ) ((-21194151347069669875047383 / 12500000000000000000000000000) : ℝ) := by
  have hlo : ((-339106421553114718088507527 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_9_rounded_endpoints.1
  have hhi : (manuscriptNormP4_9Interval.2 : ℝ) ≤ ((-21194151347069669875047383 / 12500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_9_exact_interval.1, manuscriptNormP4_9_exact_interval.2.trans hhi⟩

def manuscriptNormP5_0Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 0 (0, 0)).1

def manuscriptNormP5_0Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormP5_0Arg).re

def manuscriptNormP5_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) (0) (1) (243521 / 160000) (-111 / 689)

private theorem manuscriptNormP5_0_arg_eq : manuscriptNormP5_0Arg = barrierComplex (1 / 1) (289 / 400) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_0Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_0_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_0_exact_interval :
    manuscriptNormP5_0Term ∈ Set.Icc (manuscriptNormP5_0Interval.1 : ℝ) (manuscriptNormP5_0Interval.2 : ℝ) := by
  unfold manuscriptNormP5_0Term
  rw [manuscriptNormP5_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2875428436063 / 5000000000000000) (2802770610277 / 1000000000000000)
    manuscriptNormP5_0Arg (0) (1) (243521 / 160000) (689 / 400) (-111 / 400)
  have hratio : ((-111 / 400) / (689 / 400) : ℚ) = (-111 / 689) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_0Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_0_rounded_endpoints :
    (-1874379120731079543064084237 / 1000000000000000000000000000000) ≤ manuscriptNormP5_0Interval.1 ∧ manuscriptNormP5_0Interval.2 ≤ (-117148695045692465091096139 / 62500000000000000000000000000) := by
  simp only [manuscriptNormP5_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_0_enclosure :
    manuscriptNormP5_0Term ∈ Set.Icc ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
  have hlo : ((-1874379120731079543064084237 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_0_rounded_endpoints.1
  have hhi : (manuscriptNormP5_0Interval.2 : ℝ) ≤ ((-117148695045692465091096139 / 62500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_0_exact_interval.1, manuscriptNormP5_0_exact_interval.2.trans hhi⟩

def manuscriptNormP5_1Arg : ℂ :=
  1 - (barrierP2Tail.getD 5 (0, 0)).1 * (barrierP2Tail.getD 1 (0, 0)).1

def manuscriptNormP5_1Term : ℝ :=
  (-((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) *
    Complex.log manuscriptNormP5_1Arg).re

def manuscriptNormP5_1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) (0) (1) (1638401 / 1000000) (-201 / 1799)

private theorem manuscriptNormP5_1_arg_eq : manuscriptNormP5_1Arg = barrierComplex (1 / 1) (799 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP5_1Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP5_1_weight_eq :
    -((barrierP2Tail.getD 5 (0, 0)).2 * (barrierP2Tail.getD 1 (0, 0)).2) =
      barrierComplex (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP5_1_exact_interval :
    manuscriptNormP5_1Term ∈ Set.Icc (manuscriptNormP5_1Interval.1 : ℝ) (manuscriptNormP5_1Interval.2 : ℝ) := by
  unfold manuscriptNormP5_1Term
  rw [manuscriptNormP5_1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2637591701359 / 20000000000000000) (2570943658261 / 4000000000000000)
    manuscriptNormP5_1Arg (0) (1) (1638401 / 1000000) (1799 / 1000) (-201 / 1000)
  have hratio : ((-201 / 1000) / (1799 / 1000) : ℚ) = (-201 / 1799) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP5_1Interval
  apply h
  all_goals
    try rw [manuscriptNormP5_1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP5_1_rounded_endpoints :
    (-465843978124225478021104641 / 1000000000000000000000000000000) ≤ manuscriptNormP5_1Interval.1 ∧ manuscriptNormP5_1Interval.2 ≤ (-465843978124225454720526203 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP5_1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP5_1_enclosure :
    manuscriptNormP5_1Term ∈ Set.Icc ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-465843978124225478021104641 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP5_1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_1_rounded_endpoints.1
  have hhi : (manuscriptNormP5_1Interval.2 : ℝ) ≤ ((-465843978124225454720526203 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP5_1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP5_1_exact_interval.1, manuscriptNormP5_1_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
