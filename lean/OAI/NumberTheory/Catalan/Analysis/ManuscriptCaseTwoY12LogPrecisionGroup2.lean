import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY12

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y12YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (7930675282629144832081 / 5000000000000000000000) (9500000000 / 88546175991)

private theorem manuscriptCase2Y12YV7_arg_eq : barrierCase2Y12YV7LogArg = barrierComplex (19 / 100) (-88546175991 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV7LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV7Interval.1 : ℝ) (manuscriptCase2Y12YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y12YV7LogArg).re ∈ _
  rw [manuscriptCase2Y12YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y12YV7LogArg (1) (-2) (7930675282629144832081 / 5000000000000000000000) (88546175991 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (88546175991 / 25000000000) : ℚ) = (9500000000 / 88546175991) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV7_rounded_endpoints :
    (-326288063036080317249759821285401265767 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV7Interval.1 ∧ manuscriptCase2Y12YV7Interval.2 ≤ (-261030450428864231890458416574202523731 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-326288063036080317249759821285401265767 / 2500000000000000000000000000000000000000) : ℝ) ((-261030450428864231890458416574202523731 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-326288063036080317249759821285401265767 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV7Interval.2 : ℝ) ≤ ((-261030450428864231890458416574202523731 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV7_exact_interval.1, manuscriptCase2Y12YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y12YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (3538931634397763365668481 / 2000000000000000000000000) (87975000000 / 1879146623809)

private theorem manuscriptCase2Y12YV9_arg_eq : barrierCase2Y12YV9LogArg = barrierComplex (3519 / 40000) (-1879146623809 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV9LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV9Interval.1 : ℝ) (manuscriptCase2Y12YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y12YV9LogArg).re ∈ _
  rw [manuscriptCase2Y12YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y12YV9LogArg (1) (-2) (3538931634397763365668481 / 2000000000000000000000000) (1879146623809 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1879146623809 / 500000000000) : ℚ) = (87975000000 / 1879146623809) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV9_rounded_endpoints :
    (1119208729829674149462790989665266240649 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV9Interval.1 ∧ manuscriptCase2Y12YV9Interval.2 ≤ (34975272807177318520935438964103353137 / 312500000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((1119208729829674149462790989665266240649 / 10000000000000000000000000000000000000000) : ℝ) ((34975272807177318520935438964103353137 / 312500000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1119208729829674149462790989665266240649 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV9Interval.2 : ℝ) ≤ ((34975272807177318520935438964103353137 / 312500000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV9_exact_interval.1, manuscriptCase2Y12YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y12YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (1464810836722176940303129 / 781250000000000000000000) (19840000000 / 1210131071877)

private theorem manuscriptCase2Y12YV11_arg_eq : barrierCase2Y12YV11LogArg = barrierComplex (496 / 15625) (-1210131071877 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y12YV11LogArg, Case2PointData.Y12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y12YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y12YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y12YV11Interval.1 : ℝ) (manuscriptCase2Y12YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y12YV11LogArg).re ∈ _
  rw [manuscriptCase2Y12YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y12YV11LogArg (1) (-2) (1464810836722176940303129 / 781250000000000000000000) (1210131071877 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (1210131071877 / 312500000000) : ℚ) = (19840000000 / 1210131071877) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y12YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y12YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y12YV11_rounded_endpoints :
    (-1755669998540754623471022496524097121383 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y12YV11Interval.1 ∧ manuscriptCase2Y12YV11Interval.2 ≤ (-438917499635188636184790360349927733857 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y12YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y12YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y12 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-1755669998540754623471022496524097121383 / 10000000000000000000000000000000000000000) : ℝ) ((-438917499635188636184790360349927733857 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1755669998540754623471022496524097121383 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y12YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y12YV11Interval.2 : ℝ) ≤ ((-438917499635188636184790360349927733857 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y12YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y12YV11_exact_interval.1, manuscriptCase2Y12YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
