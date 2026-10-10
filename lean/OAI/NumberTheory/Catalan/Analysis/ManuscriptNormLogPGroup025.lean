import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP7_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP7_6Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP7_6Arg).re

def manuscriptNormP7_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2252997732537 / 1000000000000000) (0 / 1) (-6) (0) (329132164 / 244140625) (0 / 1)

private theorem manuscriptNormP7_6_arg_eq : manuscriptNormP7_6Arg = barrierComplex (9071 / 62500) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_6_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (-2252997732537 / 1000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_6_exact_interval :
    manuscriptNormP7_6Term ∈ Set.Icc (manuscriptNormP7_6Interval.1 : ℝ) (manuscriptNormP7_6Interval.2 : ℝ) := by
  unfold manuscriptNormP7_6Term
  rw [manuscriptNormP7_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2252997732537 / 1000000000000000) (0 / 1)
    manuscriptNormP7_6Arg (-6) (0) (329132164 / 244140625) (9071 / 62500) (0 / 1)
  have hratio : ((0 / 1) / (9071 / 62500) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_6_rounded_endpoints :
    (869694995447530821302128753 / 200000000000000000000000000000) ≤ manuscriptNormP7_6Interval.1 ∧ manuscriptNormP7_6Interval.2 ≤ (4348474977237654107423445337 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP7_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_6_enclosure :
    manuscriptNormP7_6Term ∈ Set.Icc ((869694995447530821302128753 / 200000000000000000000000000000) : ℝ) ((4348474977237654107423445337 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((869694995447530821302128753 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_6_rounded_endpoints.1
  have hhi : (manuscriptNormP7_6Interval.2 : ℝ) ≤ ((4348474977237654107423445337 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_6_exact_interval.1, manuscriptNormP7_6_exact_interval.2.trans hhi⟩

def manuscriptNormP7_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP7_7Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP7_7Arg).re

def manuscriptNormP7_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2165837981751 / 1250000000000000) (7200437692203 / 5000000000000000) (1) (0) (13307283041 / 7812500000) (10580 / 114871)

private theorem manuscriptNormP7_7_arg_eq : manuscriptNormP7_7Arg = barrierComplex (114871 / 62500) (529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_7_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (2165837981751 / 1250000000000000) (7200437692203 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_7_exact_interval :
    manuscriptNormP7_7Term ∈ Set.Icc (manuscriptNormP7_7Interval.1 : ℝ) (manuscriptNormP7_7Interval.2 : ℝ) := by
  unfold manuscriptNormP7_7Term
  rw [manuscriptNormP7_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2165837981751 / 1250000000000000) (7200437692203 / 5000000000000000)
    manuscriptNormP7_7Arg (1) (0) (13307283041 / 7812500000) (114871 / 62500) (529 / 3125)
  have hratio : ((529 / 3125) / (114871 / 62500) : ℚ) = (10580 / 114871) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_7_rounded_endpoints :
    (464816257410730250422934689 / 500000000000000000000000000000) ≤ manuscriptNormP7_7Interval.1 ∧ manuscriptNormP7_7Interval.2 ≤ (929632514821460500962879519 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP7_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_7_enclosure :
    manuscriptNormP7_7Term ∈ Set.Icc ((464816257410730250422934689 / 500000000000000000000000000000) : ℝ) ((929632514821460500962879519 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((464816257410730250422934689 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_7_rounded_endpoints.1
  have hhi : (manuscriptNormP7_7Interval.2 : ℝ) ≤ ((929632514821460500962879519 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_7_exact_interval.1, manuscriptNormP7_7_exact_interval.2.trans hhi⟩

def manuscriptNormP7_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP7_8Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP7_8Arg).re

def manuscriptNormP7_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) (-5) (-1) (429066082 / 244140625) (-451 / 20709)

private theorem manuscriptNormP7_8_arg_eq : manuscriptNormP7_8Arg = barrierComplex (10129 / 62500) (-529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_8_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_8_exact_interval :
    manuscriptNormP7_8Term ∈ Set.Icc (manuscriptNormP7_8Interval.1 : ℝ) (manuscriptNormP7_8Interval.2 : ℝ) := by
  unfold manuscriptNormP7_8Term
  rw [manuscriptNormP7_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7437685121511 / 4000000000000000) (4812646447989 / 4000000000000000)
    manuscriptNormP7_8Arg (-5) (-1) (429066082 / 244140625) (20709 / 62500) (-451 / 62500)
  have hratio : ((-451 / 62500) / (20709 / 62500) : ℚ) = (-451 / 20709) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_8_rounded_endpoints :
    (-1726739613144089201383812039 / 1000000000000000000000000000000) ≤ manuscriptNormP7_8Interval.1 ∧ manuscriptNormP7_8Interval.2 ≤ (-345347922628817831427739889 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP7_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_8_enclosure :
    manuscriptNormP7_8Term ∈ Set.Icc ((-1726739613144089201383812039 / 1000000000000000000000000000000) : ℝ) ((-345347922628817831427739889 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-1726739613144089201383812039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_8_rounded_endpoints.1
  have hhi : (manuscriptNormP7_8Interval.2 : ℝ) ≤ ((-345347922628817831427739889 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_8_exact_interval.1, manuscriptNormP7_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
