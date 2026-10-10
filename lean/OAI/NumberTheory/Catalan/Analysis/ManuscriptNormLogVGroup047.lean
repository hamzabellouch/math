import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV10_11Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 11 (0, 0)).1

def manuscriptNormV10_11Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) *
    Complex.log manuscriptNormV10_11Arg).re

def manuscriptNormV10_11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) (-9) (0) (18168392 / 9765625) (0 / 1)

private theorem manuscriptNormV10_11_arg_eq : manuscriptNormV10_11Arg = barrierComplex (1507 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_11Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_11_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 11 (0, 0)).2) =
      barrierComplex (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_11_exact_interval :
    manuscriptNormV10_11Term ∈ Set.Icc (manuscriptNormV10_11Interval.1 : ℝ) (manuscriptNormV10_11Interval.2 : ℝ) := by
  unfold manuscriptNormV10_11Term
  rw [manuscriptNormV10_11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (68110340912023 / 10000000000000000) (7554608004191 / 2500000000000000)
    manuscriptNormV10_11Arg (-9) (0) (18168392 / 9765625) (1507 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (1507 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_11Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_11_rounded_endpoints :
    (-9565262706655637646952898537 / 500000000000000000000000000000) ≤ manuscriptNormV10_11Interval.1 ∧ manuscriptNormV10_11Interval.2 ≤ (-19130525413311275289756496657 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV10_11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_11_enclosure :
    manuscriptNormV10_11Term ∈ Set.Icc ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-9565262706655637646952898537 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_11_rounded_endpoints.1
  have hhi : (manuscriptNormV10_11Interval.2 : ℝ) ≤ ((-19130525413311275289756496657 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_11_exact_interval.1, manuscriptNormV10_11_exact_interval.2.trans hhi⟩

def manuscriptNormV10_12Arg : ℂ :=
  1 - (barrierV2Tail.getD 10 (0, 0)).1 * (barrierV2Tail.getD 12 (0, 0)).1

def manuscriptNormV10_12Term : ℝ :=
  (-((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) *
    Complex.log manuscriptNormV10_12Arg).re

def manuscriptNormV10_12Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) (1) (0) (2351571049 / 1250000000) (0 / 1)

private theorem manuscriptNormV10_12_arg_eq : manuscriptNormV10_12Arg = barrierComplex (48493 / 25000) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormV10_12Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV10_12_weight_eq :
    -((barrierV2Tail.getD 10 (0, 0)).2 * (barrierV2Tail.getD 12 (0, 0)).2) =
      barrierComplex (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV10_12_exact_interval :
    manuscriptNormV10_12Term ∈ Set.Icc (manuscriptNormV10_12Interval.1 : ℝ) (manuscriptNormV10_12Interval.2 : ℝ) := by
  unfold manuscriptNormV10_12Term
  rw [manuscriptNormV10_12_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2391875533 / 390625000000) (-8491908331363 / 2000000000000000)
    manuscriptNormV10_12Arg (1) (0) (2351571049 / 1250000000) (48493 / 25000) (0 / 1)
  have hratio : ((0 / 1) / (48493 / 25000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV10_12Interval
  apply h
  all_goals
    try rw [manuscriptNormV10_12_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV10_12_rounded_endpoints :
    (-1014222019038597977530548497 / 250000000000000000000000000000) ≤ manuscriptNormV10_12Interval.1 ∧ manuscriptNormV10_12Interval.2 ≤ (-2028444038077195954845955103 / 500000000000000000000000000000) := by
  simp only [manuscriptNormV10_12Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV10_12_enclosure :
    manuscriptNormV10_12Term ∈ Set.Icc ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-1014222019038597977530548497 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormV10_12Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_12_rounded_endpoints.1
  have hhi : (manuscriptNormV10_12Interval.2 : ℝ) ≤ ((-2028444038077195954845955103 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV10_12_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV10_12_exact_interval.1, manuscriptNormV10_12_exact_interval.2.trans hhi⟩

def manuscriptNormV11_0Arg : ℂ :=
  1 - (barrierV2Tail.getD 11 (0, 0)).1 * (barrierV2Tail.getD 0 (0, 0)).1

def manuscriptNormV11_0Term : ℝ :=
  (-((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) *
    Complex.log manuscriptNormV11_0Arg).re

def manuscriptNormV11_0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) (0) (1) (632689 / 390625) (-133 / 1117)

private theorem manuscriptNormV11_0_arg_eq : manuscriptNormV11_0Arg = barrierComplex (1 / 1) (492 / 625) := by
  apply Complex.ext <;> norm_num [manuscriptNormV11_0Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV11_0_weight_eq :
    -((barrierV2Tail.getD 11 (0, 0)).2 * (barrierV2Tail.getD 0 (0, 0)).2) =
      barrierComplex (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV11_0_exact_interval :
    manuscriptNormV11_0Term ∈ Set.Icc (manuscriptNormV11_0Interval.1 : ℝ) (manuscriptNormV11_0Interval.2 : ℝ) := by
  unfold manuscriptNormV11_0Term
  rw [manuscriptNormV11_0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-31237616036943 / 20000000000000000) (-330063770995139 / 20000000000000000)
    manuscriptNormV11_0Arg (0) (1) (632689 / 390625) (1117 / 625) (-133 / 625)
  have hratio : ((-133 / 625) / (1117 / 625) : ℚ) = (-133 / 1117) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV11_0Interval
  apply h
  all_goals
    try rw [manuscriptNormV11_0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV11_0_rounded_endpoints :
    (10629171334454979986482737241 / 1000000000000000000000000000000) ≤ manuscriptNormV11_0Interval.1 ∧ manuscriptNormV11_0Interval.2 ≤ (10629171334454980584759307369 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV11_0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV11_0_enclosure :
    manuscriptNormV11_0Term ∈ Set.Icc ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((10629171334454979986482737241 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV11_0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_0_rounded_endpoints.1
  have hhi : (manuscriptNormV11_0Interval.2 : ℝ) ≤ ((10629171334454980584759307369 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV11_0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV11_0_exact_interval.1, manuscriptNormV11_0_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
