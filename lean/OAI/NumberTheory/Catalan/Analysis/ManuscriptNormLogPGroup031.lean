import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP9_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP9_4Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP9_4Arg).re

def manuscriptNormP9_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) (-5) (0) (1340981 / 781250) (391 / 1090)

private theorem manuscriptNormP9_4_arg_eq : manuscriptNormP9_4Arg = barrierComplex (109 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_4_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_4_exact_interval :
    manuscriptNormP9_4Term ∈ Set.Icc (manuscriptNormP9_4Interval.1 : ℝ) (manuscriptNormP9_4Interval.2 : ℝ) := by
  unfold manuscriptNormP9_4Term
  rw [manuscriptNormP9_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (51978482934179 / 40000000000000000) (-23836077867557 / 40000000000000000)
    manuscriptNormP9_4Arg (-5) (0) (1340981 / 781250) (109 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (109 / 500) : ℚ) = (391 / 1090) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_4_rounded_endpoints :
    (-339106421553114718088507527 / 200000000000000000000000000000) ≤ manuscriptNormP9_4Interval.1 ∧ manuscriptNormP9_4Interval.2 ≤ (-21194151347069669875047383 / 12500000000000000000000000000) := by
  simp only [manuscriptNormP9_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_4_enclosure :
    manuscriptNormP9_4Term ∈ Set.Icc ((-339106421553114718088507527 / 200000000000000000000000000000) : ℝ) ((-21194151347069669875047383 / 12500000000000000000000000000) : ℝ) := by
  have hlo : ((-339106421553114718088507527 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_4_rounded_endpoints.1
  have hhi : (manuscriptNormP9_4Interval.2 : ℝ) ≤ ((-21194151347069669875047383 / 12500000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_4_exact_interval.1, manuscriptNormP9_4_exact_interval.2.trans hhi⟩

def manuscriptNormP9_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP9_5Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP9_5Arg).re

def manuscriptNormP9_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP9_5_arg_eq : manuscriptNormP9_5Arg = barrierComplex (891 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_5_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_5_exact_interval :
    manuscriptNormP9_5Term ∈ Set.Icc (manuscriptNormP9_5Interval.1 : ℝ) (manuscriptNormP9_5Interval.2 : ℝ) := by
  unfold manuscriptNormP9_5Term
  rw [manuscriptNormP9_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-57165053974051 / 40000000000000000) (1441492417883 / 40000000000000000)
    manuscriptNormP9_5Arg (1) (0) (79540981 / 50000000) (891 / 500) (-391 / 5000)
  have hratio : ((-391 / 5000) / (891 / 500) : ℚ) = (-391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_5_rounded_endpoints :
    (-825452530567521026167866743 / 1000000000000000000000000000000) ≤ manuscriptNormP9_5Interval.1 ∧ manuscriptNormP9_5Interval.2 ≤ (-412726265283760513035682481 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP9_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_5_enclosure :
    manuscriptNormP9_5Term ∈ Set.Icc ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_5_rounded_endpoints.1
  have hhi : (manuscriptNormP9_5Interval.2 : ℝ) ≤ ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_5_exact_interval.1, manuscriptNormP9_5_exact_interval.2.trans hhi⟩

def manuscriptNormP9_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 9 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP9_6Term : ℝ :=
  (-((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP9_6Arg).re

def manuscriptNormP9_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) (-5) (1) (429066082 / 244140625) (451 / 20709)

private theorem manuscriptNormP9_6_arg_eq : manuscriptNormP9_6Arg = barrierComplex (10129 / 62500) (529 / 3125) := by
  apply Complex.ext <;> norm_num [manuscriptNormP9_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP9_6_weight_eq :
    -((barrierP2Tail.getD 9 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP9_6_exact_interval :
    manuscriptNormP9_6Term ∈ Set.Icc (manuscriptNormP9_6Interval.1 : ℝ) (manuscriptNormP9_6Interval.2 : ℝ) := by
  unfold manuscriptNormP9_6Term
  rw [manuscriptNormP9_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7437685121511 / 4000000000000000) (-4812646447989 / 4000000000000000)
    manuscriptNormP9_6Arg (-5) (1) (429066082 / 244140625) (20709 / 62500) (451 / 62500)
  have hratio : ((451 / 62500) / (20709 / 62500) : ℚ) = (451 / 20709) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP9_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP9_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP9_6_rounded_endpoints :
    (-1726739613144089201383812039 / 1000000000000000000000000000000) ≤ manuscriptNormP9_6Interval.1 ∧ manuscriptNormP9_6Interval.2 ≤ (-345347922628817831427739889 / 200000000000000000000000000000) := by
  simp only [manuscriptNormP9_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP9_6_enclosure :
    manuscriptNormP9_6Term ∈ Set.Icc ((-1726739613144089201383812039 / 1000000000000000000000000000000) : ℝ) ((-345347922628817831427739889 / 200000000000000000000000000000) : ℝ) := by
  have hlo : ((-1726739613144089201383812039 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP9_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_6_rounded_endpoints.1
  have hhi : (manuscriptNormP9_6Interval.2 : ℝ) ≤ ((-345347922628817831427739889 / 200000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP9_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP9_6_exact_interval.1, manuscriptNormP9_6_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
