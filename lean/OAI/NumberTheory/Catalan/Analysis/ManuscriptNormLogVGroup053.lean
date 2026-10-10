import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV12_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV12_3Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV12_3Arg).re

def manuscriptNormV12_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) (0) (1) (11711569 / 6250000) (-163 / 4837)

private theorem manuscriptNormV12_3_arg_eq : manuscriptNormV12_3Arg = barrierComplex (1 / 1) (2337 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_3_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_3_exact_interval :
    manuscriptNormV12_3Term ∈ Set.Icc (manuscriptNormV12_3Interval.1 : ℝ) (manuscriptNormV12_3Interval.2 : ℝ) := by
  unfold manuscriptNormV12_3Term
  rw [manuscriptNormV12_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (5068806760521 / 10000000000000000) (-53558167558133 / 10000000000000000)
    manuscriptNormV12_3Arg (0) (1) (11711569 / 6250000) (4837 / 2500) (-163 / 2500)
  have hratio : ((-163 / 2500) / (4837 / 2500) : ℚ) = (-163 / 4837) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_3_rounded_endpoints :
    (4185192971723380656657287637 / 1000000000000000000000000000000) ≤ manuscriptNormV12_3Interval.1 ∧ manuscriptNormV12_3Interval.2 ≤ (418519297172338085081844233 / 100000000000000000000000000000) := by
  simp only [manuscriptNormV12_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_3_enclosure :
    manuscriptNormV12_3Term ∈ Set.Icc ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((4185192971723380656657287637 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_3_rounded_endpoints.1
  have hhi : (manuscriptNormV12_3Interval.2 : ℝ) ≤ ((418519297172338085081844233 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_3_exact_interval.1, manuscriptNormV12_3_exact_interval.2.trans hhi⟩

def manuscriptNormV12_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV12_4Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV12_4Arg).re

def manuscriptNormV12_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) (0) (1) (473027266 / 244140625) (-248 / 15377)

private theorem manuscriptNormV12_4_arg_eq : manuscriptNormV12_4Arg = barrierComplex (1 / 1) (15129 / 15625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_4_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_4_exact_interval :
    manuscriptNormV12_4Term ∈ Set.Icc (manuscriptNormV12_4Interval.1 : ℝ) (manuscriptNormV12_4Interval.2 : ℝ) := by
  unfold manuscriptNormV12_4Term
  rw [manuscriptNormV12_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-23877787302441 / 20000000000000000) (252298143070293 / 20000000000000000)
    manuscriptNormV12_4Arg (0) (1) (473027266 / 244140625) (30754 / 15625) (-496 / 15625)
  have hratio : ((-496 / 15625) / (30754 / 15625) : ℚ) = (-248 / 15377) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_4_rounded_endpoints :
    (-5049556952780585057360689577 / 500000000000000000000000000000) ≤ manuscriptNormV12_4Interval.1 ∧ manuscriptNormV12_4Interval.2 ≤ (-10099113905561169657387514651 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_4_enclosure :
    manuscriptNormV12_4Term ∈ Set.Icc ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5049556952780585057360689577 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_4_rounded_endpoints.1
  have hhi : (manuscriptNormV12_4Interval.2 : ℝ) ≤ ((-10099113905561169657387514651 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_4_exact_interval.1, manuscriptNormV12_4_exact_interval.2.trans hhi⟩

def manuscriptNormV12_5Arg : ℂ :=
  1 - (barrierV2Tail.getD 12 (0, 0)).1 * (barrierV2Tail.getD 5 (0, 0)).1

def manuscriptNormV12_5Term : ℝ :=
  (-((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormV12_5Arg).re

def manuscriptNormV12_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) (-5) (0) (16889672 / 9765625) (0 / 1)

private theorem manuscriptNormV12_5_arg_eq : manuscriptNormV12_5Arg = barrierComplex (1453 / 6250) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV12_5Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV12_5_weight_eq :
    -((barrierV2Tail.getD 12 (0, 0)).2 * (barrierV2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV12_5_exact_interval :
    manuscriptNormV12_5Term ∈ Set.Icc (manuscriptNormV12_5Interval.1 : ℝ) (manuscriptNormV12_5Interval.2 : ℝ) := by
  unfold manuscriptNormV12_5Term
  rw [manuscriptNormV12_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-445455465826873 / 20000000000000000) (256246551143909 / 20000000000000000)
    manuscriptNormV12_5Arg (-5) (0) (16889672 / 9765625) (1453 / 6250) (0 / 1)
  have hratio : ((0 / 1) / (1453 / 6250) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV12_5Interval
  apply h
  all_goals
    try rw [manuscriptNormV12_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV12_5_rounded_endpoints :
    (4061860828661937773552758353 / 125000000000000000000000000000) ≤ manuscriptNormV12_5Interval.1 ∧ manuscriptNormV12_5Interval.2 ≤ (32494886629295502195942314237 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV12_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV12_5_enclosure :
    manuscriptNormV12_5Term ∈ Set.Icc ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((4061860828661937773552758353 / 125000000000000000000000000000) : ℝ) ≤ (manuscriptNormV12_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_5_rounded_endpoints.1
  have hhi : (manuscriptNormV12_5Interval.2 : ℝ) ≤ ((32494886629295502195942314237 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV12_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV12_5_exact_interval.1, manuscriptNormV12_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
