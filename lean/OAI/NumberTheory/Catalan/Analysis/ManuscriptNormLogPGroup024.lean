import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP7_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP7_3Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP7_3Arg).re

def manuscriptNormP7_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-249342691992771 / 20000000000000000) (244406797738203 / 20000000000000000) (1) (0) (16918021 / 12500000) (161 / 4110)

private theorem manuscriptNormP7_3_arg_eq : manuscriptNormP7_3Arg = barrierComplex (411 / 250) (161 / 2500) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_3_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-249342691992771 / 20000000000000000) (244406797738203 / 20000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_3_exact_interval :
    manuscriptNormP7_3Term ∈ Set.Icc (manuscriptNormP7_3Interval.1 : ℝ) (manuscriptNormP7_3Interval.2 : ℝ) := by
  unfold manuscriptNormP7_3Term
  rw [manuscriptNormP7_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-249342691992771 / 20000000000000000) (244406797738203 / 20000000000000000)
    manuscriptNormP7_3Arg (1) (0) (16918021 / 12500000) (411 / 250) (161 / 2500)
  have hratio : ((161 / 2500) / (411 / 250) : ℚ) = (161 / 4110) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_3_rounded_endpoints :
    (-6685833039281012505245132349 / 1000000000000000000000000000000) ≤ manuscriptNormP7_3Interval.1 ∧ manuscriptNormP7_3Interval.2 ≤ (-6685833039281012504403289509 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP7_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_3_enclosure :
    manuscriptNormP7_3Term ∈ Set.Icc ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-6685833039281012505245132349 / 1000000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_3_rounded_endpoints.1
  have hhi : (manuscriptNormP7_3Interval.2 : ℝ) ≤ ((-6685833039281012504403289509 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_3_exact_interval.1, manuscriptNormP7_3_exact_interval.2.trans hhi⟩

def manuscriptNormP7_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP7_4Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP7_4Arg).re

def manuscriptNormP7_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) (-5) (-1) (1340981 / 781250) (699 / 1481)

private theorem manuscriptNormP7_4_arg_eq : manuscriptNormP7_4Arg = barrierComplex (109 / 500) (-391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_4_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_4_exact_interval :
    manuscriptNormP7_4Term ∈ Set.Icc (manuscriptNormP7_4Interval.1 : ℝ) (manuscriptNormP7_4Interval.2 : ℝ) := by
  unfold manuscriptNormP7_4Term
  rw [manuscriptNormP7_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-14391556077387 / 10000000000000000) (-1045946527347 / 5000000000000000)
    manuscriptNormP7_4Arg (-5) (-1) (1340981 / 781250) (1481 / 5000) (699 / 5000)
  have hratio : ((699 / 5000) / (1481 / 5000) : ℚ) = (699 / 1481) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_4_rounded_endpoints :
    (508264464717646502930370657 / 250000000000000000000000000000) ≤ manuscriptNormP7_4Interval.1 ∧ manuscriptNormP7_4Interval.2 ≤ (63533058089705813132507881 / 31250000000000000000000000000) := by
  simp only [manuscriptNormP7_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_4_enclosure :
    manuscriptNormP7_4Term ∈ Set.Icc ((508264464717646502930370657 / 250000000000000000000000000000) : ℝ) ((63533058089705813132507881 / 31250000000000000000000000000) : ℝ) := by
  have hlo : ((508264464717646502930370657 / 250000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_4_rounded_endpoints.1
  have hhi : (manuscriptNormP7_4Interval.2 : ℝ) ≤ ((63533058089705813132507881 / 31250000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_4_exact_interval.1, manuscriptNormP7_4_exact_interval.2.trans hhi⟩

def manuscriptNormP7_5Arg : ℂ :=
  1 - (barrierP2Tail.getD 7 (0, 0)).1 * (barrierP2Tail.getD 5 (0, 0)).1

def manuscriptNormP7_5Term : ℝ :=
  (-((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) *
    Complex.log manuscriptNormP7_5Arg).re

def manuscriptNormP7_5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) (1) (0) (79540981 / 50000000) (391 / 8910)

private theorem manuscriptNormP7_5_arg_eq : manuscriptNormP7_5Arg = barrierComplex (891 / 500) (391 / 5000) := by
  apply Complex.ext <;> norm_num [manuscriptNormP7_5Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP7_5_weight_eq :
    -((barrierP2Tail.getD 7 (0, 0)).2 * (barrierP2Tail.getD 5 (0, 0)).2) =
      barrierComplex (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP7_5_exact_interval :
    manuscriptNormP7_5Term ∈ Set.Icc (manuscriptNormP7_5Interval.1 : ℝ) (manuscriptNormP7_5Interval.2 : ℝ) := by
  unfold manuscriptNormP7_5Term
  rw [manuscriptNormP7_5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (6202476756039 / 5000000000000000) (7590127221861 / 10000000000000000)
    manuscriptNormP7_5Arg (1) (0) (79540981 / 50000000) (891 / 500) (391 / 5000)
  have hratio : ((391 / 5000) / (891 / 500) : ℚ) = (391 / 8910) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP7_5Interval
  apply h
  all_goals
    try rw [manuscriptNormP7_5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP7_5_rounded_endpoints :
    (136917181857232359070005731 / 200000000000000000000000000000) ≤ manuscriptNormP7_5Interval.1 ∧ manuscriptNormP7_5Interval.2 ≤ (1095337454857858872694069 / 1600000000000000000000000000) := by
  simp only [manuscriptNormP7_5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP7_5_enclosure :
    manuscriptNormP7_5Term ∈ Set.Icc ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
  have hlo : ((136917181857232359070005731 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP7_5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_5_rounded_endpoints.1
  have hhi : (manuscriptNormP7_5Interval.2 : ℝ) ≤ ((1095337454857858872694069 / 1600000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP7_5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP7_5_exact_interval.1, manuscriptNormP7_5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
