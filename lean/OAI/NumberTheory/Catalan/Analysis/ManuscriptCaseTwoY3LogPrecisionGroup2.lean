import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY3

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y3YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-4) (-1) (212247697269864427729 / 156250000000000000000) (-1545256777 / 20545256777)

private theorem manuscriptCase2Y3YV7_arg_eq : barrierCase2Y3YV7LogArg = barrierComplex (19 / 100) (-11045256777 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV7LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV7Interval.1 : ℝ) (manuscriptCase2Y3YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y3YV7LogArg).re ∈ _
  rw [manuscriptCase2Y3YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y3YV7LogArg (-4) (-1) (212247697269864427729 / 156250000000000000000) (20545256777 / 50000000000) (-1545256777 / 50000000000)
  have hratio : ((-1545256777 / 50000000000) / (20545256777 / 50000000000) : ℚ) = (-1545256777 / 20545256777) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV7_rounded_endpoints :
    (-3231232607953694582019038785993770049493 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV7Interval.1 ∧ manuscriptCase2Y3YV7Interval.2 ≤ (-807808151988423631718827932771998853993 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-3231232607953694582019038785993770049493 / 10000000000000000000000000000000000000000) : ℝ) ((-807808151988423631718827932771998853993 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-3231232607953694582019038785993770049493 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV7Interval.2 : ℝ) ≤ ((-807808151988423631718827932771998853993 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV7_exact_interval.1, manuscriptCase2Y3YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y3YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-4) (-2) (62685254873171903555329 / 62500000000000000000000) (87975000000 / 234404893823)

private theorem manuscriptCase2Y3YV9_arg_eq : barrierCase2Y3YV9LogArg = barrierComplex (3519 / 40000) (-234404893823 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV9LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV9Interval.1 : ℝ) (manuscriptCase2Y3YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y3YV9LogArg).re ∈ _
  rw [manuscriptCase2Y3YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y3YV9LogArg (-4) (-2) (62685254873171903555329 / 62500000000000000000000) (234404893823 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (234404893823 / 500000000000) : ℚ) = (87975000000 / 234404893823) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV9_rounded_endpoints :
    (258269196422493982917637361463586732667 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV9Interval.1 ∧ manuscriptCase2Y3YV9Interval.2 ≤ (129134598211247013096284388904763421259 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((258269196422493982917637361463586732667 / 10000000000000000000000000000000000000000) : ℝ) ((129134598211247013096284388904763421259 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((258269196422493982917637361463586732667 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV9Interval.2 : ℝ) ≤ ((129134598211247013096284388904763421259 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV9_exact_interval.1, manuscriptCase2Y3YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y3YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-5) (-2) (23180084390071344779161 / 12207031250000000000000) (19840000000 / 150951842619)

private theorem manuscriptCase2Y3YV11_arg_eq : barrierCase2Y3YV11LogArg = barrierComplex (496 / 15625) (-150951842619 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y3YV11LogArg, Case2PointData.Y3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y3YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y3YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y3YV11Interval.1 : ℝ) (manuscriptCase2Y3YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y3YV11LogArg).re ∈ _
  rw [manuscriptCase2Y3YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y3YV11LogArg (-5) (-2) (23180084390071344779161 / 12207031250000000000000) (150951842619 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (150951842619 / 312500000000) : ℚ) = (19840000000 / 150951842619) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y3YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y3YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y3YV11_rounded_endpoints :
    (-709271077009334680456131474808925009721 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y3YV11Interval.1 ∧ manuscriptCase2Y3YV11Interval.2 ≤ (-4432944231308341506726282426138752943 / 31250000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y3YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y3YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-709271077009334680456131474808925009721 / 5000000000000000000000000000000000000000) : ℝ) ((-4432944231308341506726282426138752943 / 31250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-709271077009334680456131474808925009721 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y3YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y3YV11Interval.2 : ℝ) ≤ ((-4432944231308341506726282426138752943 / 31250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y3YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y3YV11_exact_interval.1, manuscriptCase2Y3YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
