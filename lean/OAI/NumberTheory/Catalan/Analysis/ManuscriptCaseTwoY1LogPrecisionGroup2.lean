import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY1

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y1YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-5) (0) (24776412851185094929 / 19531250000000000000) (-1487922327 / 4750000000)

private theorem manuscriptCase2Y1YV7_arg_eq : barrierCase2Y1YV7LogArg = barrierComplex (19 / 100) (-1487922327 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV7LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV7Interval.1 : ℝ) (manuscriptCase2Y1YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y1YV7LogArg).re ∈ _
  rw [manuscriptCase2Y1YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y1YV7LogArg (-5) (0) (24776412851185094929 / 19531250000000000000) (19 / 100) (-1487922327 / 25000000000)
  have hratio : ((-1487922327 / 25000000000) / (19 / 100) : ℚ) = (-1487922327 / 4750000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV7_rounded_endpoints :
    (-2987328500848754835132281920380306312787 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV7Interval.1 ∧ manuscriptCase2Y1YV7Interval.2 ≤ (-119493140033950193384128220276245664371 / 400000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-2987328500848754835132281920380306312787 / 10000000000000000000000000000000000000000) : ℝ) ((-119493140033950193384128220276245664371 / 400000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2987328500848754835132281920380306312787 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV7Interval.2 : ℝ) ≤ ((-119493140033950193384128220276245664371 / 400000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV7_exact_interval.1, manuscriptCase2Y1YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y1YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-7) (-1) (2932008239263375902529 / 1953125000000000000000) (12410481727 / 75564518273)

private theorem manuscriptCase2Y1YV9_arg_eq : barrierCase2Y1YV9LogArg = barrierComplex (3519 / 40000) (-31577018273 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV9LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV9Interval.1 : ℝ) (manuscriptCase2Y1YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y1YV9LogArg).re ∈ _
  rw [manuscriptCase2Y1YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y1YV9LogArg (-7) (-1) (2932008239263375902529 / 1953125000000000000000) (75564518273 / 500000000000) (12410481727 / 500000000000)
  have hratio : ((12410481727 / 500000000000) / (75564518273 / 500000000000) : ℚ) = (12410481727 / 75564518273) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV9_rounded_endpoints :
    (-373112147955973225395364145223596683101 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV9Interval.1 ∧ manuscriptCase2Y1YV9Interval.2 ≤ (-373112147955973203644911629353904659679 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-373112147955973225395364145223596683101 / 10000000000000000000000000000000000000000) : ℝ) ((-373112147955973203644911629353904659679 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-373112147955973225395364145223596683101 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV9Interval.2 : ℝ) ≤ ((-373112147955973203644911629353904659679 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV9_exact_interval.1, manuscriptCase2Y1YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y1YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-8) (-2) (511916122538016063961 / 381469726562500000000) (9920000000 / 20334938469)

private theorem manuscriptCase2Y1YV11_arg_eq : barrierCase2Y1YV11LogArg = barrierComplex (496 / 15625) (-20334938469 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y1YV11LogArg, Case2PointData.Y1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y1YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y1YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y1YV11Interval.1 : ℝ) (manuscriptCase2Y1YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y1YV11LogArg).re ∈ _
  rw [manuscriptCase2Y1YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y1YV11LogArg (-8) (-2) (511916122538016063961 / 381469726562500000000) (20334938469 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (20334938469 / 156250000000) : ℚ) = (9920000000 / 20334938469) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y1YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y1YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y1YV11_rounded_endpoints :
    (-942955506871485414438107322127392954081 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y1YV11Interval.1 ∧ manuscriptCase2Y1YV11Interval.2 ≤ (-942955506871485323889373287237961751331 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y1YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y1YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y1 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-942955506871485414438107322127392954081 / 10000000000000000000000000000000000000000) : ℝ) ((-942955506871485323889373287237961751331 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-942955506871485414438107322127392954081 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y1YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y1YV11Interval.2 : ℝ) ≤ ((-942955506871485323889373287237961751331 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y1YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y1YV11_exact_interval.1, manuscriptCase2Y1YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
