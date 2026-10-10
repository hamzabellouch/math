import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y9YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (1) (-2) (5315789812542217924921 / 5000000000000000000000) (9500000000 / 72287895339)

private theorem manuscriptCase2Y9YV7_arg_eq : barrierCase2Y9YV7LogArg = barrierComplex (19 / 100) (-72287895339 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV7LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV7Interval.1 : ℝ) (manuscriptCase2Y9YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y9YV7LogArg).re ∈ _
  rw [manuscriptCase2Y9YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y9YV7LogArg (1) (-2) (5315789812542217924921 / 5000000000000000000000) (72287895339 / 25000000000) (19 / 50)
  have hratio : ((19 / 50) / (72287895339 / 25000000000) : ℚ) = (9500000000 / 72287895339) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV7_rounded_endpoints :
    (-1582697391403764788137784376381746464617 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV7Interval.1 ∧ manuscriptCase2Y9YV7Interval.2 ≤ (-1582697391403764678591037236859875739703 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-1582697391403764788137784376381746464617 / 10000000000000000000000000000000000000000) : ℝ) ((-1582697391403764678591037236859875739703 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1582697391403764788137784376381746464617 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV7Interval.2 : ℝ) ≤ ((-1582697391403764678591037236859875739703 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV7_exact_interval.1, manuscriptCase2Y9YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y9YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (29325000000 / 511369926287)

private theorem manuscriptCase2Y9YV9_arg_eq : barrierCase2Y9YV9LogArg = barrierComplex (3519 / 40000) (-1534109778861 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV9LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV9Interval.1 : ℝ) (manuscriptCase2Y9YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y9YV9LogArg).re ∈ _
  rw [manuscriptCase2Y9YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y9YV9LogArg (1) (-2) (2361232414221946322457321 / 2000000000000000000000000) (1534109778861 / 500000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (1534109778861 / 500000000000) : ℚ) = (29325000000 / 511369926287) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV9_rounded_endpoints :
    (1045242179360712073321130974034991362147 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV9Interval.1 ∧ manuscriptCase2Y9YV9Interval.2 ≤ (1045242179360712116528248228408373399603 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((1045242179360712073321130974034991362147 / 10000000000000000000000000000000000000000) : ℝ) ((1045242179360712116528248228408373399603 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1045242179360712073321130974034991362147 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV9Interval.2 : ℝ) ≤ ((1045242179360712116528248228408373399603 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV9_exact_interval.1, manuscriptCase2Y9YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y9YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (1) (-2) (976408339475940925754689 / 781250000000000000000000) (19840000000 / 987934569633)

private theorem manuscriptCase2Y9YV11_arg_eq : barrierCase2Y9YV11LogArg = barrierComplex (496 / 15625) (-987934569633 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y9YV11LogArg, Case2PointData.Y9, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y9YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y9YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y9YV11Interval.1 : ℝ) (manuscriptCase2Y9YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y9YV11LogArg).re ∈ _
  rw [manuscriptCase2Y9YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y9YV11LogArg (1) (-2) (976408339475940925754689 / 781250000000000000000000) (987934569633 / 312500000000) (992 / 15625)
  have hratio : ((992 / 15625) / (987934569633 / 312500000000) : ℚ) = (19840000000 / 987934569633) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y9YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y9YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y9YV11_rounded_endpoints :
    (-865413857661589162875636056450749237309 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y9YV11Interval.1 ∧ manuscriptCase2Y9YV11Interval.2 ≤ (-346165543064635649403929095689659889081 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y9YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y9YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y9 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-865413857661589162875636056450749237309 / 5000000000000000000000000000000000000000) : ℝ) ((-346165543064635649403929095689659889081 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-865413857661589162875636056450749237309 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y9YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y9YV11Interval.2 : ℝ) ≤ ((-346165543064635649403929095689659889081 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y9YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y9YV11_exact_interval.1, manuscriptCase2Y9YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
