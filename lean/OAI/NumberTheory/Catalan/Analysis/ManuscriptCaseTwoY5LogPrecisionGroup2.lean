import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY5

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y5YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-2) (-2) (13169656341620988001 / 9765625000000000000) (1187500000 / 3429212751)

private theorem manuscriptCase2Y5YV7_arg_eq : barrierCase2Y5YV7LogArg = barrierComplex (19 / 100) (-3429212751 / 6250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV7LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV7Interval.1 : ℝ) (manuscriptCase2Y5YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y5YV7LogArg).re ∈ _
  rw [manuscriptCase2Y5YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y5YV7LogArg (-2) (-2) (13169656341620988001 / 9765625000000000000) (3429212751 / 3125000000) (19 / 50)
  have hratio : ((19 / 50) / (3429212751 / 3125000000) : ℚ) = (1187500000 / 3429212751) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV7_rounded_endpoints :
    (-54394296999185516386093780147894779091 / 200000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV7Interval.1 ∧ manuscriptCase2Y5YV7Interval.2 ≤ (-27197148499592757096521257524533127791 / 100000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-54394296999185516386093780147894779091 / 200000000000000000000000000000000000000) : ℝ) ((-27197148499592757096521257524533127791 / 100000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-54394296999185516386093780147894779091 / 200000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV7Interval.2 : ℝ) ≤ ((-27197148499592757096521257524533127791 / 100000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV7_exact_interval.1, manuscriptCase2Y5YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y5YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-2) (-2) (5417206850412850472401 / 3906250000000000000000) (10996875000 / 72775515049)

private theorem manuscriptCase2Y5YV9_arg_eq : barrierCase2Y5YV9LogArg = barrierComplex (3519 / 40000) (-72775515049 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV9LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV9Interval.1 : ℝ) (manuscriptCase2Y5YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y5YV9LogArg).re ∈ _
  rw [manuscriptCase2Y5YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y5YV9LogArg (-2) (-2) (5417206850412850472401 / 3906250000000000000000) (72775515049 / 62500000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (72775515049 / 62500000000) : ℚ) = (10996875000 / 72775515049) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV9_rounded_endpoints :
    (669000523248878747993309139615200850483 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV9Interval.1 ∧ manuscriptCase2Y5YV9Interval.2 ≤ (669000523248878791223025453764644971669 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((669000523248878747993309139615200850483 / 10000000000000000000000000000000000000000) : ℝ) ((669000523248878791223025453764644971669 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((669000523248878747993309139615200850483 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV9Interval.2 : ℝ) ≤ ((669000523248878791223025453764644971669 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV9_exact_interval.1, manuscriptCase2Y5YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y5YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-2) (-2) (2202563694890542314409 / 1525878906250000000000) (2480000000 / 46865907597)

private theorem manuscriptCase2Y5YV11_arg_eq : barrierCase2Y5YV11LogArg = barrierComplex (496 / 15625) (-46865907597 / 78125000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y5YV11LogArg, Case2PointData.Y5, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y5YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y5YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y5YV11Interval.1 : ℝ) (manuscriptCase2Y5YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y5YV11LogArg).re ∈ _
  rw [manuscriptCase2Y5YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y5YV11LogArg (-2) (-2) (2202563694890542314409 / 1525878906250000000000) (46865907597 / 39062500000) (992 / 15625)
  have hratio : ((992 / 15625) / (46865907597 / 39062500000) : ℚ) = (2480000000 / 46865907597) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y5YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y5YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y5YV11_rounded_endpoints :
    (-39894662368477840295708767394618191867 / 250000000000000000000000000000000000000) ≤ manuscriptCase2Y5YV11Interval.1 ∧ manuscriptCase2Y5YV11Interval.2 ≤ (-797893247369556766544892575969976817579 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y5YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y5YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y5 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-39894662368477840295708767394618191867 / 250000000000000000000000000000000000000) : ℝ) ((-797893247369556766544892575969976817579 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-39894662368477840295708767394618191867 / 250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y5YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y5YV11Interval.2 : ℝ) ≤ ((-797893247369556766544892575969976817579 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y5YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y5YV11_exact_interval.1, manuscriptCase2Y5YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
