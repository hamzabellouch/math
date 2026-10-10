import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV3_6Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 6 (0, 0)).1

def manuscriptNormV3_6Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormV3_6Arg).re

def manuscriptNormV3_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) (0) (1) (1549081 / 1000000) (-259 / 1741)

private theorem manuscriptNormV3_6_arg_eq : manuscriptNormV3_6Arg = barrierComplex (1 / 1) (741 / 1000) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_6Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_6_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 6 (0, 0)).2) =
      barrierComplex (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_6_exact_interval :
    manuscriptNormV3_6Term ∈ Set.Icc (manuscriptNormV3_6Interval.1 : ℝ) (manuscriptNormV3_6Interval.2 : ℝ) := by
  unfold manuscriptNormV3_6Term
  rw [manuscriptNormV3_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (33589651698169 / 5000000000000000) (-1481637471433 / 156250000000000)
    manuscriptNormV3_6Arg (0) (1) (1549081 / 1000000) (1741 / 1000) (-259 / 1000)
  have hratio : ((-259 / 1000) / (1741 / 1000) : ℚ) = (-259 / 1741) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_6Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_6_rounded_endpoints :
    (7517221743037368858959427589 / 1000000000000000000000000000000) ≤ manuscriptNormV3_6Interval.1 ∧ manuscriptNormV3_6Interval.2 ≤ (1879305435759342300679999343 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV3_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_6_enclosure :
    manuscriptNormV3_6Term ∈ Set.Icc ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((7517221743037368858959427589 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_6_rounded_endpoints.1
  have hhi : (manuscriptNormV3_6Interval.2 : ℝ) ≤ ((1879305435759342300679999343 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_6_exact_interval.1, manuscriptNormV3_6_exact_interval.2.trans hhi⟩

def manuscriptNormV3_7Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 7 (0, 0)).1

def manuscriptNormV3_7Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormV3_7Arg).re

def manuscriptNormV3_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371)

private theorem manuscriptNormV3_7_arg_eq : manuscriptNormV3_7Arg = barrierComplex (1 / 1) (-171 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_7Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_7_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_7_exact_interval :
    manuscriptNormV3_7Term ∈ Set.Icc (manuscriptNormV3_7Interval.1 : ℝ) (manuscriptNormV3_7Interval.2 : ℝ) := by
  unfold manuscriptNormV3_7Term
  rw [manuscriptNormV3_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000)
    manuscriptNormV3_7Arg (0) (-1) (69241 / 40000) (371 / 200) (29 / 200)
  have hratio : ((29 / 200) / (371 / 200) : ℚ) = (29 / 371) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_7Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_7_rounded_endpoints :
    (3146180457411023770175562599 / 1000000000000000000000000000000) ≤ manuscriptNormV3_7Interval.1 ∧ manuscriptNormV3_7Interval.2 ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_7_enclosure :
    manuscriptNormV3_7Term ∈ Set.Icc ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_7_rounded_endpoints.1
  have hhi : (manuscriptNormV3_7Interval.2 : ℝ) ≤ ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_7_exact_interval.1, manuscriptNormV3_7_exact_interval.2.trans hhi⟩

def manuscriptNormV3_8Arg : ℂ :=
  1 - (barrierV2Tail.getD 3 (0, 0)).1 * (barrierV2Tail.getD 8 (0, 0)).1

def manuscriptNormV3_8Term : ℝ :=
  (-((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormV3_8Arg).re

def manuscriptNormV3_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) (0) (1) (69241 / 40000) (-29 / 371)

private theorem manuscriptNormV3_8_arg_eq : manuscriptNormV3_8Arg = barrierComplex (1 / 1) (171 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormV3_8Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV3_8_weight_eq :
    -((barrierV2Tail.getD 3 (0, 0)).2 * (barrierV2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV3_8_exact_interval :
    manuscriptNormV3_8Term ∈ Set.Icc (manuscriptNormV3_8Interval.1 : ℝ) (manuscriptNormV3_8Interval.2 : ℝ) := by
  unfold manuscriptNormV3_8Term
  rw [manuscriptNormV3_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-19324262066907 / 2500000000000000) (-37227558060581 / 5000000000000000)
    manuscriptNormV3_8Arg (0) (1) (69241 / 40000) (371 / 200) (-29 / 200)
  have hratio : ((-29 / 200) / (371 / 200) : ℚ) = (-29 / 371) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV3_8Interval
  apply h
  all_goals
    try rw [manuscriptNormV3_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV3_8_rounded_endpoints :
    (3146180457411023770175562599 / 1000000000000000000000000000000) ≤ manuscriptNormV3_8Interval.1 ∧ manuscriptNormV3_8Interval.2 ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV3_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV3_8_enclosure :
    manuscriptNormV3_8Term ∈ Set.Icc ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV3_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_8_rounded_endpoints.1
  have hhi : (manuscriptNormV3_8Interval.2 : ℝ) ≤ ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV3_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV3_8_exact_interval.1, manuscriptNormV3_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
