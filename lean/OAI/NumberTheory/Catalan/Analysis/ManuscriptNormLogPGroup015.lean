import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP4_6Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 6 (0, 0)).1

def manuscriptNormP4_6Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) *
    Complex.log manuscriptNormP4_6Arg).re

def manuscriptNormP4_6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (-391 / 8910)

private theorem manuscriptNormP4_6_arg_eq : manuscriptNormP4_6Arg = barrierComplex (891 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_6Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_6_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 6 (0, 0)).2) =
      barrierComplex (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_6_exact_interval :
    manuscriptNormP4_6Term ∈ Set.Icc (manuscriptNormP4_6Interval.1 : ℝ) (manuscriptNormP4_6Interval.2 : ℝ) := by
  unfold manuscriptNormP4_6Term
  rw [manuscriptNormP4_6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (6202476756039 / 5000000000000000) (-7590127221861 / 10000000000000000)
    manuscriptNormP4_6Arg (1) (0) (79540981 / 50000000) (891 / 500) (-391 / 5000)
  have hratio : ((-391 / 5000) / (891 / 500) : ℚ) = (-391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_6Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_6_rounded_endpoints :
    (136917181857232359070005731 / 200000000000000000000000000000) ≤ manuscriptNormP4_6Interval.1 ∧ manuscriptNormP4_6Interval.2 ≤ (1095337454857858872694069 / 1600000000000000000000000000) := by
  simp only [manuscriptNormP4_6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_6_enclosure :
    manuscriptNormP4_6Term ∈ Set.Icc ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
  have hlo : ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_6_rounded_endpoints.1
  have hhi : (manuscriptNormP4_6Interval.2 : ℝ) ≤ ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_6_exact_interval.1, manuscriptNormP4_6_exact_interval.2.trans hhi⟩

def manuscriptNormP4_7Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 7 (0, 0)).1

def manuscriptNormP4_7Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) *
    Complex.log manuscriptNormP4_7Arg).re

def manuscriptNormP4_7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP4_7_arg_eq : manuscriptNormP4_7Arg = barrierComplex (109 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_7Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_7_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 7 (0, 0)).2) =
      barrierComplex (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_7_exact_interval :
    manuscriptNormP4_7Term ∈ Set.Icc (manuscriptNormP4_7Interval.1 : ℝ) (manuscriptNormP4_7Interval.2 : ℝ) := by
  unfold manuscriptNormP4_7Term
  rw [manuscriptNormP4_7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000)
    manuscriptNormP4_7Arg (-5) (-1) (1340981 / 781250) (1481 / 5000) (699 / 5000)
  have hratio : ((699 / 5000) / (1481 / 5000) : ℚ) = (699 / 1481) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_7Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_7_rounded_endpoints :
    (508264464717646502930370657 / 250000000000000000000000000000) ≤ manuscriptNormP4_7Interval.1 ∧ manuscriptNormP4_7Interval.2 ≤ (63533058089705813132507881 / 31250000000000000000000000000) := by
  simp only [manuscriptNormP4_7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_7_enclosure :
    manuscriptNormP4_7Term ∈ Set.Icc ((508264464717646502930370657 / 250000000000000000000000000000) : ℝ) ((63533058089705813132507881 / 31250000000000000000000000000) : ℝ) := by
  have hlo : ((508264464717646502930370657 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_7_rounded_endpoints.1
  have hhi : (manuscriptNormP4_7Interval.2 : ℝ) ≤ ((63533058089705813132507881 / 31250000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_7_exact_interval.1, manuscriptNormP4_7_exact_interval.2.trans hhi⟩

def manuscriptNormP4_8Arg : ℂ :=
  1 - (barrierP2Tail.getD 4 (0, 0)).1 * (barrierP2Tail.getD 8 (0, 0)).1

def manuscriptNormP4_8Term : ℝ :=
  (-((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) *
    Complex.log manuscriptNormP4_8Arg).re

def manuscriptNormP4_8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP4_8_arg_eq : manuscriptNormP4_8Arg = barrierComplex (891 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP4_8Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP4_8_weight_eq :
    -((barrierP2Tail.getD 4 (0, 0)).2 * (barrierP2Tail.getD 8 (0, 0)).2) =
      barrierComplex (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP4_8_exact_interval :
    manuscriptNormP4_8Term ∈ Set.Icc (manuscriptNormP4_8Interval.1 : ℝ) (manuscriptNormP4_8Interval.2 : ℝ) := by
  unfold manuscriptNormP4_8Term
  rw [manuscriptNormP4_8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-57165053974051 / 40000000000000000) (-1441492417883 / 40000000000000000)
    manuscriptNormP4_8Arg (1) (0) (79540981 / 50000000) (891 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (891 / 500) : ℚ) = (391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP4_8Interval
  apply h
  all_goals
    try rw [manuscriptNormP4_8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP4_8_rounded_endpoints :
    (-825452530567521026167866743 / 1000000000000000000000000000000) ≤ manuscriptNormP4_8Interval.1 ∧ manuscriptNormP4_8Interval.2 ≤ (-412726265283760513035682481 / 500000000000000000000000000000) := by
  simp only [manuscriptNormP4_8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP4_8_enclosure :
    manuscriptNormP4_8Term ∈ Set.Icc ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
  have hlo : ((-825452530567521026167866743 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP4_8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_8_rounded_endpoints.1
  have hhi : (manuscriptNormP4_8Interval.2 : ℝ) ≤ ((-412726265283760513035682481 / 500000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP4_8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP4_8_exact_interval.1, manuscriptNormP4_8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
