import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV11_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV11_4Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV11_4Arg).re

def manuscriptNormV11_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) (0) (-1) (473027266 / 244140625) (248 / 15377)

private theorem manuscriptNormV11_4_arg_eq : manuscriptNormV11_4Arg = barrierComplex (1 / 1) (-15129 / 15625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_4_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_4_exact_interval :
    manuscriptNormV11_4Term ∈ Set.Icc (manuscriptNormV11_4Interval.1 : ℝ) (manuscriptNormV11_4Interval.2 : ℝ) := by
  unfold manuscriptNormV11_4Term
  rw [manuscriptNormV11_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-23877787302441 / 20000000000000000) (-252298143070293 / 20000000000000000)
    manuscriptNormV11_4Arg (0) (-1) (473027266 / 244140625) (30754 / 15625) (496 / 15625)
  have hratio : ((496 / 15625) / (30754 / 15625) : ℚ) = (248 / 15377) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_4_rounded_endpoints :
    (-5049556952780585057360689577 / 500000000000000000000000000000) ≤ manuscriptNormV11_4Interval.1 ∧ manuscriptNormV11_4Interval.2 ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_4_enclosure :
    manuscriptNormV11_4Term ∈ Set.Icc ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_4_rounded_endpoints.1
  have hhi : (manuscriptNormV11_4Interval.2 : ℝ) ≤ ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_4_exact_interval.1, manuscriptNormV11_4_exact_interval.2.trans hhi⟩

def manuscriptNormV11_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV11_5Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV11_5Arg).re

def manuscriptNormV11_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) (1) (0) (122036209 / 78125000) (0 / 1)

private theorem manuscriptNormV11_5_arg_eq : manuscriptNormV11_5Arg = barrierComplex (11047 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_5_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_5_exact_interval :
    manuscriptNormV11_5Term ∈ Set.Icc (manuscriptNormV11_5Interval.1 : ℝ) (manuscriptNormV11_5Interval.2 : ℝ) := by
  unfold manuscriptNormV11_5Term
  rw [manuscriptNormV11_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (389474106710791 / 20000000000000000) (-335265249034277 / 20000000000000000)
    manuscriptNormV11_5Arg (1) (0) (122036209 / 78125000) (11047 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (11047 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_5_rounded_endpoints :
    (2218356623650128240239486083 / 200000000000000000000000000000) ≤ manuscriptNormV11_5Interval.1 ∧ manuscriptNormV11_5Interval.2 ≤ (5545891559125320601256195969 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV11_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_5_enclosure :
    manuscriptNormV11_5Term ∈ Set.Icc ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((2218356623650128240239486083 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_5_rounded_endpoints.1
  have hhi : (manuscriptNormV11_5Interval.2 : ℝ) ≤ ((5545891559125320601256195969 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_5_exact_interval.1, manuscriptNormV11_5_exact_interval.2.trans hhi⟩

def manuscriptNormV11_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV11_6Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV11_6Arg).re

def manuscriptNormV11_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV11_6_arg_eq : manuscriptNormV11_6Arg = barrierComplex (1453 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_6_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_6_exact_interval :
    manuscriptNormV11_6Term ∈ Set.Icc (manuscriptNormV11_6Interval.1 : ℝ) (manuscriptNormV11_6Interval.2 : ℝ) := by
  unfold manuscriptNormV11_6Term
  rw [manuscriptNormV11_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-445455465826873 / 20000000000000000) (-256246551143909 / 20000000000000000)
    manuscriptNormV11_6Arg (-5) (0) (16889672 / 9765625) (1453 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (1453 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_6_rounded_endpoints :
    (4061860828661937773552758353 / 125000000000000000000000000000) ≤ manuscriptNormV11_6Interval.1 ∧ manuscriptNormV11_6Interval.2 ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_6_enclosure :
    manuscriptNormV11_6Term ∈ Set.Icc ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_6_rounded_endpoints.1
  have hhi : (manuscriptNormV11_6Interval.2 : ℝ) ≤ ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_6_exact_interval.1, manuscriptNormV11_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
