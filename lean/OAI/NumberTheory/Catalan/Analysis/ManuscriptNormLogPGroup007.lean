import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptNormP2_2Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 2 (0, 0)).1

def manuscriptNormP2_2Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) *
    Complex.log manuscriptNormP2_2Arg).re

def manuscriptNormP2_2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) (1) (0) (22201 / 20000) (0 / 1)

private theorem manuscriptNormP2_2_arg_eq : manuscriptNormP2_2Arg = barrierComplex (149 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_2Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_2_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 2 (0, 0)).2) =
      barrierComplex (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_2_exact_interval :
    manuscriptNormP2_2Term ∈ Set.Icc (manuscriptNormP2_2Interval.1 : ℝ) (manuscriptNormP2_2Interval.2 : ℝ) := by
  unfold manuscriptNormP2_2Term
  rw [manuscriptNormP2_2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3374669985148323 / 40000000000000000) (1057383684695809 / 10000000000000000)
    manuscriptNormP2_2Arg (1) (0) (22201 / 20000) (149 / 100) (0 / 1)
  have hratio : ((0 / 1) / (149 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_2Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_2_rounded_endpoints :
    (-6728689014070180867221453861 / 200000000000000000000000000000) ≤ manuscriptNormP2_2Interval.1 ∧ manuscriptNormP2_2Interval.2 ≤ (-3364344507035090433041040741 / 100000000000000000000000000000) := by
  simp only [manuscriptNormP2_2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_2_enclosure :
    manuscriptNormP2_2Term ∈ Set.Icc ((-6728689014070180867221453861 / 200000000000000000000000000000) : ℝ) ((-3364344507035090433041040741 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((-6728689014070180867221453861 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_2_rounded_endpoints.1
  have hhi : (manuscriptNormP2_2Interval.2 : ℝ) ≤ ((-3364344507035090433041040741 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_2_exact_interval.1, manuscriptNormP2_2_exact_interval.2.trans hhi⟩

def manuscriptNormP2_3Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 3 (0, 0)).1

def manuscriptNormP2_3Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) *
    Complex.log manuscriptNormP2_3Arg).re

def manuscriptNormP2_3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1082171180825569 / 8000000000000000) (0 / 1) (-2) (0) (2601 / 2500) (0 / 1)

private theorem manuscriptNormP2_3_arg_eq : manuscriptNormP2_3Arg = barrierComplex (51 / 100) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_3Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_3_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 3 (0, 0)).2) =
      barrierComplex (-1082171180825569 / 8000000000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_3_exact_interval :
    manuscriptNormP2_3Term ∈ Set.Icc (manuscriptNormP2_3Interval.1 : ℝ) (manuscriptNormP2_3Interval.2 : ℝ) := by
  unfold manuscriptNormP2_3Term
  rw [manuscriptNormP2_3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1082171180825569 / 8000000000000000) (0 / 1)
    manuscriptNormP2_3Arg (-2) (0) (2601 / 2500) (51 / 100) (0 / 1)
  have hratio : ((0 / 1) / (51 / 100) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_3Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_3_rounded_endpoints :
    (45542129394244653502391507333 / 500000000000000000000000000000) ≤ manuscriptNormP2_3Interval.1 ∧ manuscriptNormP2_3Interval.2 ≤ (91084258788489307023051407697 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP2_3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_3_enclosure :
    manuscriptNormP2_3Term ∈ Set.Icc ((45542129394244653502391507333 / 500000000000000000000000000000) : ℝ) ((91084258788489307023051407697 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((45542129394244653502391507333 / 500000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_3_rounded_endpoints.1
  have hhi : (manuscriptNormP2_3Interval.2 : ℝ) ≤ ((91084258788489307023051407697 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_3_exact_interval.1, manuscriptNormP2_3_exact_interval.2.trans hhi⟩

def manuscriptNormP2_4Arg : ℂ :=
  1 - (barrierP2Tail.getD 2 (0, 0)).1 * (barrierP2Tail.getD 4 (0, 0)).1

def manuscriptNormP2_4Term : ℝ :=
  (-((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) *
    Complex.log manuscriptNormP2_4Arg).re

def manuscriptNormP2_4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) (1) (0) (101761 / 80000) (0 / 1)

private theorem manuscriptNormP2_4_arg_eq : manuscriptNormP2_4Arg = barrierComplex (319 / 200) (0 / 1) := by
  apply Complex.ext <;> norm_num [manuscriptNormP2_4Arg, barrierP2Tail,
    barrierConjugatePair, barrierComplex]

private theorem manuscriptNormP2_4_weight_eq :
    -((barrierP2Tail.getD 2 (0, 0)).2 * (barrierP2Tail.getD 4 (0, 0)).2) =
      barrierComplex (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptNormP2_4_exact_interval :
    manuscriptNormP2_4Term ∈ Set.Icc (manuscriptNormP2_4Interval.1 : ℝ) (manuscriptNormP2_4Interval.2 : ℝ) := by
  unfold manuscriptNormP2_4Term
  rw [manuscriptNormP2_4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-273161078429227 / 40000000000000000) (-358543847837271 / 40000000000000000)
    manuscriptNormP2_4Arg (1) (0) (101761 / 80000) (319 / 200) (0 / 1)
  have hratio : ((0 / 1) / (319 / 200) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptNormP2_4Interval
  apply h
  all_goals
    try rw [manuscriptNormP2_4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptNormP2_4_rounded_endpoints :
    (-127531733280728920730965549 / 40000000000000000000000000000) ≤ manuscriptNormP2_4Interval.1 ∧ manuscriptNormP2_4Interval.2 ≤ (-3188293332018223017813008911 / 1000000000000000000000000000000) := by
  simp only [manuscriptNormP2_4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptNormP2_4_enclosure :
    manuscriptNormP2_4Term ∈ Set.Icc ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-127531733280728920730965549 / 40000000000000000000000000000) : ℝ) ≤ (manuscriptNormP2_4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_4_rounded_endpoints.1
  have hhi : (manuscriptNormP2_4Interval.2 : ℝ) ≤ ((-3188293332018223017813008911 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptNormP2_4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptNormP2_4_exact_interval.1, manuscriptNormP2_4_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
