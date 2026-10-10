import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX9

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X9XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2547524013509477505841 / 2500000000000000000000) (-6893766279 / 50000000000)

private theorem manuscriptCase2X9XV7_arg_eq : barrierCase2X9XV7LogArg = barrierComplex (1 / 1) (-6893766279 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV7LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV7Interval.1 : ℝ) (manuscriptCase2X9XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X9XV7LogArg).re ∈ _
  rw [manuscriptCase2X9XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X9XV7LogArg (0) (0) (2547524013509477505841 / 2500000000000000000000) (1 / 1) (-6893766279 / 50000000000)
  have hratio : ((-6893766279 / 50000000000) / (1 / 1) : ℚ) = (-6893766279 / 50000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV7_rounded_endpoints :
    (192055810055078861625714556618814468931 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV7Interval.1 ∧ manuscriptCase2X9XV7Interval.2 ≤ (48013952513769715406428639154703617233 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((192055810055078861625714556618814468931 / 10000000000000000000000000000000000000000) : ℝ) ((48013952513769715406428639154703617233 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((192055810055078861625714556618814468931 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV7Interval.2 : ℝ) ≤ ((48013952513769715406428639154703617233 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV7_exact_interval.1, manuscriptCase2X9XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1021403994281966035686241 / 1000000000000000000000000) (-146301039921 / 1000000000000)

private theorem manuscriptCase2X9XV9_arg_eq : barrierCase2X9XV9LogArg = barrierComplex (1 / 1) (-146301039921 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV9LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV9Interval.1 : ℝ) (manuscriptCase2X9XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X9XV9LogArg).re ∈ _
  rw [manuscriptCase2X9XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X9XV9LogArg (0) (0) (1021403994281966035686241 / 1000000000000000000000000) (1 / 1) (-146301039921 / 1000000000000)
  have hratio : ((-146301039921 / 1000000000000) / (1 / 1) : ℚ) = (-146301039921 / 1000000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV9_rounded_endpoints :
    (-90068835914486378234184548701716966969 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV9Interval.1 ∧ manuscriptCase2X9XV9Interval.2 ≤ (-11258604489310797279273068587714620871 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-90068835914486378234184548701716966969 / 10000000000000000000000000000000000000000) : ℝ) ((-11258604489310797279273068587714620871 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-90068835914486378234184548701716966969 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV9Interval.2 : ℝ) ≤ ((-11258604489310797279273068587714620871 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV9_exact_interval.1, manuscriptCase2X9XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (399501429634381298590969 / 390625000000000000000000) (-94214805813 / 625000000000)

private theorem manuscriptCase2X9XV11_arg_eq : barrierCase2X9XV11LogArg = barrierComplex (1 / 1) (-94214805813 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XV11LogArg, Case2PointData.X9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XV11Interval.1 : ℝ) (manuscriptCase2X9XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X9XV11LogArg).re ∈ _
  rw [manuscriptCase2X9XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X9XV11LogArg (0) (0) (399501429634381298590969 / 390625000000000000000000) (1 / 1) (-94214805813 / 625000000000)
  have hratio : ((-94214805813 / 625000000000) / (1 / 1) : ℚ) = (-94214805813 / 625000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XV11_rounded_endpoints :
    (163607699290078412500443460699778456483 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XV11Interval.1 ∧ manuscriptCase2X9XV11Interval.2 ≤ (40901924822519603125110865174944614121 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((163607699290078412500443460699778456483 / 10000000000000000000000000000000000000000) : ℝ) ((40901924822519603125110865174944614121 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((163607699290078412500443460699778456483 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XV11Interval.2 : ℝ) ≤ ((40901924822519603125110865174944614121 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XV11_exact_interval.1, manuscriptCase2X9XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
