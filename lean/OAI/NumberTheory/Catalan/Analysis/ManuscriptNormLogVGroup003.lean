import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV0_9Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 9 (0, 0)).1

def manuscriptNormV0_9Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) *
    Complex.log manuscriptNormV0_9Arg).re

def manuscriptNormV0_9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) (0) (1) (98981 / 62500) (-59 / 441)

private theorem manuscriptNormV0_9_arg_eq : manuscriptNormV0_9Arg = barrierComplex (1 / 1) (191 / 250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_9Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_9_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 9 (0, 0)).2) =
      barrierComplex (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_9_exact_interval :
    manuscriptNormV0_9Term ∈ Set.Icc (manuscriptNormV0_9Interval.1 : ℝ) (manuscriptNormV0_9Interval.2 : ℝ) := by
  unfold manuscriptNormV0_9Term
  rw [manuscriptNormV0_9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (50868278597681 / 10000000000000000) (90528431015797 / 10000000000000000)
    manuscriptNormV0_9Arg (0) (1) (98981 / 62500) (441 / 250) (-59 / 250)
  have hratio : ((-59 / 250) / (441 / 250) : ℚ) = (-59 / 441) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_9Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_9_rounded_endpoints :
    (-9251408280602598306119171 / 1953125000000000000000000000) ≤ manuscriptNormV0_9Interval.1 ∧ manuscriptNormV0_9Interval.2 ≤ (-592090129958566250568464173 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV0_9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_9_enclosure :
    manuscriptNormV0_9Term ∈ Set.Icc ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ≤ (manuscriptNormV0_9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_9_rounded_endpoints.1
  have hhi : (manuscriptNormV0_9Interval.2 : ℝ) ≤ ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_9_exact_interval.1, manuscriptNormV0_9_exact_interval.2.trans hhi⟩

def manuscriptNormV0_10Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 10 (0, 0)).1

def manuscriptNormV0_10Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) *
    Complex.log manuscriptNormV0_10Arg).re

def manuscriptNormV0_10Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) (0) (-1) (98981 / 62500) (59 / 441)

private theorem manuscriptNormV0_10_arg_eq : manuscriptNormV0_10Arg = barrierComplex (1 / 1) (-191 / 250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_10Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_10_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 10 (0, 0)).2) =
      barrierComplex (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_10_exact_interval :
    manuscriptNormV0_10Term ∈ Set.Icc (manuscriptNormV0_10Interval.1 : ℝ) (manuscriptNormV0_10Interval.2 : ℝ) := by
  unfold manuscriptNormV0_10Term
  rw [manuscriptNormV0_10_weight_eq]
  have h := manuscript_weighted_complex_log_interval (50868278597681 / 10000000000000000) (-90528431015797 / 10000000000000000)
    manuscriptNormV0_10Arg (0) (-1) (98981 / 62500) (441 / 250) (59 / 250)
  have hratio : ((59 / 250) / (441 / 250) : ℚ) = (59 / 441) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_10Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_10_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_10_rounded_endpoints :
    (-9251408280602598306119171 / 1953125000000000000000000000) ≤ manuscriptNormV0_10Interval.1 ∧ manuscriptNormV0_10Interval.2 ≤ (-592090129958566250568464173 / 125000000000000000000000000000) := by
  simp only [manuscriptNormV0_10Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_10_enclosure :
    manuscriptNormV0_10Term ∈ Set.Icc ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
  have hlo : ((-9251408280602598306119171 / 1953125000000000000000000000) : ℝ) ≤ (manuscriptNormV0_10Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_10_rounded_endpoints.1
  have hhi : (manuscriptNormV0_10Interval.2 : ℝ) ≤ ((-592090129958566250568464173 / 125000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_10_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_10_exact_interval.1, manuscriptNormV0_10_exact_interval.2.trans hhi⟩

def manuscriptNormV0_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 0 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV0_11Term : ℝ :=
  (-((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV0_11Arg).re

def manuscriptNormV0_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117)

private theorem manuscriptNormV0_11_arg_eq : manuscriptNormV0_11Arg = barrierComplex (1 / 1) (492 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV0_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV0_11_weight_eq :
    -((barrierV2Tail.getD 0 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV0_11_exact_interval :
    manuscriptNormV0_11Term ∈ Set.Icc (manuscriptNormV0_11Interval.1 : ℝ) (manuscriptNormV0_11Interval.2 : ℝ) := by
  unfold manuscriptNormV0_11Term
  rw [manuscriptNormV0_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000)
    manuscriptNormV0_11Arg (0) (1) (632689 / 390625) (1117 / 625) (-133 / 625)
  have hratio : ((-133 / 625) / (1117 / 625) : ℚ) = (-133 / 1117) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV0_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV0_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV0_11_rounded_endpoints :
    (10629171334454979986482737241 / 1000000000000000000000000000000) ≤ manuscriptNormV0_11Interval.1 ∧ manuscriptNormV0_11Interval.2 ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV0_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV0_11_enclosure :
    manuscriptNormV0_11Term ∈ Set.Icc ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV0_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_11_rounded_endpoints.1
  have hhi : (manuscriptNormV0_11Interval.2 : ℝ) ≤ ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV0_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV0_11_exact_interval.1, manuscriptNormV0_11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
