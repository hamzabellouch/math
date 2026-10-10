import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX11

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X11XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (677105581362858928921 / 625000000000000000000) (-7218419589 / 25000000000)

private theorem manuscriptCase2X11XV7_arg_eq : barrierCase2X11XV7LogArg = barrierComplex (1 / 1) (-7218419589 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV7LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV7Interval.1 : ℝ) (manuscriptCase2X11XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X11XV7LogArg).re ∈ _
  rw [manuscriptCase2X11XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X11XV7LogArg (0) (0) (677105581362858928921 / 625000000000000000000) (1 / 1) (-7218419589 / 25000000000)
  have hratio : ((-7218419589 / 25000000000) / (1 / 1) : ℚ) = (-7218419589 / 25000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV7_rounded_endpoints :
    (90387411257982482630849936827683138381 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X11XV7Interval.1 ∧ manuscriptCase2X11XV7Interval.2 ≤ (361549645031929930523399747423770216943 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((90387411257982482630849936827683138381 / 2500000000000000000000000000000000000000) : ℝ) ((361549645031929930523399747423770216943 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((90387411257982482630849936827683138381 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV7Interval.2 : ℝ) ≤ ((361549645031929930523399747423770216943 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV7_exact_interval.1, manuscriptCase2X11XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (273467453255536501061321 / 250000000000000000000000) (-153190904611 / 500000000000)

private theorem manuscriptCase2X11XV9_arg_eq : barrierCase2X11XV9LogArg = barrierComplex (1 / 1) (-153190904611 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV9LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV9Interval.1 : ℝ) (manuscriptCase2X11XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X11XV9LogArg).re ∈ _
  rw [manuscriptCase2X11XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X11XV9LogArg (0) (0) (273467453255536501061321 / 250000000000000000000000) (1 / 1) (-153190904611 / 500000000000)
  have hratio : ((-153190904611 / 500000000000) / (1 / 1) : ℚ) = (-153190904611 / 500000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV9_rounded_endpoints :
    (-192090348150313870018275531121150221461 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV9Interval.1 ∧ manuscriptCase2X11XV9Interval.2 ≤ (-375176461231081777379444395127380267 / 19531250000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-192090348150313870018275531121150221461 / 10000000000000000000000000000000000000000) : ℝ) ((-375176461231081777379444395127380267 / 19531250000000000000000000000000000000) : ℝ) := by
  have hlo : ((-192090348150313870018275531121150221461 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV9Interval.2 : ℝ) ≤ ((-375176461231081777379444395127380267 / 19531250000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV9_exact_interval.1, manuscriptCase2X11XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (107388414696773984390689 / 97656250000000000000000) (-98651734383 / 312500000000)

private theorem manuscriptCase2X11XV11_arg_eq : barrierCase2X11XV11LogArg = barrierComplex (1 / 1) (-98651734383 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XV11LogArg, Case2PointData.X11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XV11Interval.1 : ℝ) (manuscriptCase2X11XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X11XV11LogArg).re ∈ _
  rw [manuscriptCase2X11XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X11XV11LogArg (0) (0) (107388414696773984390689 / 97656250000000000000000) (1 / 1) (-98651734383 / 312500000000)
  have hratio : ((-98651734383 / 312500000000) / (1 / 1) : ℚ) = (-98651734383 / 312500000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XV11_rounded_endpoints :
    (336899420219947952885381427284719306367 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X11XV11Interval.1 ∧ manuscriptCase2X11XV11Interval.2 ≤ (336899420219947952885381433726874703761 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X11 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((336899420219947952885381427284719306367 / 10000000000000000000000000000000000000000) : ℝ) ((336899420219947952885381433726874703761 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((336899420219947952885381427284719306367 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XV11Interval.2 : ℝ) ≤ ((336899420219947952885381433726874703761 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XV11_exact_interval.1, manuscriptCase2X11XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
