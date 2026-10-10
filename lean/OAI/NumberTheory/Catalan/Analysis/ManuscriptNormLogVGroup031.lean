import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormV7_2Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 2 (0, 0)).1

def manuscriptNormV7_2Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormV7_2Arg).re

def manuscriptNormV7_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) (0) (-1) (25426 / 15625) (13 / 112)

private theorem manuscriptNormV7_2_arg_eq : manuscriptNormV7_2Arg = barrierComplex (1 / 1) (-99 / 125) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_2Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_2_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 2 (0, 0)).2) =
      barrierComplex (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_2_exact_interval :
    manuscriptNormV7_2Term ∈ Set.Icc (manuscriptNormV7_2Interval.1 : ℝ) (manuscriptNormV7_2Interval.2 : ℝ) := by
  unfold manuscriptNormV7_2Term
  rw [manuscriptNormV7_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (9971941566429 / 2500000000000000) (-19210618876707 / 5000000000000000)
    manuscriptNormV7_2Arg (0) (-1) (25426 / 15625) (224 / 125) (26 / 125)
  have hratio : ((26 / 125) / (224 / 125) : ℚ) = (13 / 112) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_2Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_2_rounded_endpoints :
    (-801277525046095019997984753 / 500000000000000000000000000000) ≤ manuscriptNormV7_2Interval.1 ∧ manuscriptNormV7_2Interval.2 ≤ (-400638762523047475177650967 / 250000000000000000000000000000) := by
  simp only [manuscriptNormV7_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_2_enclosure :
    manuscriptNormV7_2Term ∈ Set.Icc ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
  have hlo : ((-801277525046095019997984753 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_2_rounded_endpoints.1
  have hhi : (manuscriptNormV7_2Interval.2 : ℝ) ≤ ((-400638762523047475177650967 / 250000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_2_exact_interval.1, manuscriptNormV7_2_exact_interval.2.trans hhi⟩

def manuscriptNormV7_3Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 3 (0, 0)).1

def manuscriptNormV7_3Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormV7_3Arg).re

def manuscriptNormV7_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) (0) (-1) (69241 / 40000) (29 / 371)

private theorem manuscriptNormV7_3_arg_eq : manuscriptNormV7_3Arg = barrierComplex (1 / 1) (-171 / 200) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_3Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_3_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_3_exact_interval :
    manuscriptNormV7_3Term ∈ Set.Icc (manuscriptNormV7_3Interval.1 : ℝ) (manuscriptNormV7_3Interval.2 : ℝ) := by
  unfold manuscriptNormV7_3Term
  rw [manuscriptNormV7_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-19324262066907 / 2500000000000000) (37227558060581 / 5000000000000000)
    manuscriptNormV7_3Arg (0) (-1) (69241 / 40000) (371 / 200) (29 / 200)
  have hratio : ((29 / 200) / (371 / 200) : ℚ) = (29 / 371) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_3Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_3_rounded_endpoints :
    (3146180457411023770175562599 / 1000000000000000000000000000000) ≤ manuscriptNormV7_3Interval.1 ∧ manuscriptNormV7_3Interval.2 ≤ (3146180457411024040091742511 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV7_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_3_enclosure :
    manuscriptNormV7_3Term ∈ Set.Icc ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((3146180457411023770175562599 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_3_rounded_endpoints.1
  have hhi : (manuscriptNormV7_3Interval.2 : ℝ) ≤ ((3146180457411024040091742511 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_3_exact_interval.1, manuscriptNormV7_3_exact_interval.2.trans hhi⟩

def manuscriptNormV7_4Arg : ℂ :=
  1 - (barrierV2Tail.getD 7 (0, 0)).1 * (barrierV2Tail.getD 4 (0, 0)).1

def manuscriptNormV7_4Term : ℝ :=
  (-((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormV7_4Arg).re

def manuscriptNormV7_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) (0) (-1) (2787949 / 1562500) (143 / 2357)

private theorem manuscriptNormV7_4_arg_eq : manuscriptNormV7_4Arg = barrierComplex (1 / 1) (-1107 / 1250) := by
  apply Complex.ext <;> norm_num [manuscriptNormV7_4Arg, barrierV2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormV7_4_weight_eq :
    -((barrierV2Tail.getD 7 (0, 0)).2 * (barrierV2Tail.getD 4 (0, 0)).2) =
      barrierComplex (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormV7_4_exact_interval :
    manuscriptNormV7_4Term ∈ Set.Icc (manuscriptNormV7_4Interval.1 : ℝ) (manuscriptNormV7_4Interval.2 : ℝ) := by
  unfold manuscriptNormV7_4Term
  rw [manuscriptNormV7_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (91031408615547 / 5000000000000000) (-175369027693701 / 10000000000000000)
    manuscriptNormV7_4Arg (0) (-1) (2787949 / 1562500) (2357 / 1250) (143 / 1250)
  have hratio : ((143 / 1250) / (2357 / 1250) : ℚ) = (143 / 2357) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormV7_4Interval
  apply h
  all_goals
    try rw [manuscriptNormV7_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormV7_4_rounded_endpoints :
    (-7439891480413310489970227707 / 1000000000000000000000000000000) ≤ manuscriptNormV7_4Interval.1 ∧ manuscriptNormV7_4Interval.2 ≤ (-7439891480413309854216924131 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormV7_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormV7_4_enclosure :
    manuscriptNormV7_4Term ∈ Set.Icc ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-7439891480413310489970227707 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormV7_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_4_rounded_endpoints.1
  have hhi : (manuscriptNormV7_4Interval.2 : ℝ) ≤ ((-7439891480413309854216924131 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormV7_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormV7_4_exact_interval.1, manuscriptNormV7_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
