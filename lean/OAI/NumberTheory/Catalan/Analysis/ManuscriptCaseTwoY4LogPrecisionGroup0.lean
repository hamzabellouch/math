import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY4

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y4YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (1) (0) (38436689258889534001 / 19531250000000000000) (0 / 1)

private theorem manuscriptCase2Y4YV0_arg_eq : barrierCase2Y4YV0LogArg = barrierComplex (6199732999 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV0LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV0Interval.1 : ℝ) (manuscriptCase2Y4YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y4YV0LogArg).re ∈ _
  rw [manuscriptCase2Y4YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y4YV0LogArg (1) (0) (38436689258889534001 / 19531250000000000000) (6199732999 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (6199732999 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV0_rounded_endpoints :
    (-20825106031515275251628610767755066773 / 200000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV0Interval.1 ∧ manuscriptCase2Y4YV0Interval.2 ≤ (-1041255301575763762433276189772727987851 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-20825106031515275251628610767755066773 / 200000000000000000000000000000000000000) : ℝ) ((-1041255301575763762433276189772727987851 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-20825106031515275251628610767755066773 / 200000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV0Interval.2 : ℝ) ≤ ((-1041255301575763762433276189772727987851 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV0_exact_interval.1, manuscriptCase2Y4YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y4YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (2) (0) (332577190307180806009 / 244140625000000000000) (0 / 1)

private theorem manuscriptCase2Y4YV1_arg_eq : barrierCase2Y4YV1LogArg = barrierComplex (18236698997 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV1LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV1Interval.1 : ℝ) (manuscriptCase2Y4YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y4YV1LogArg).re ∈ _
  rw [manuscriptCase2Y4YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y4YV1LogArg (2) (0) (332577190307180806009 / 244140625000000000000) (18236698997 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (18236698997 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV1_rounded_endpoints :
    (-377372274402321837274927861567266460327 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV1Interval.1 ∧ manuscriptCase2Y4YV1Interval.2 ≤ (-377372274402321837214808196588334524203 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-377372274402321837274927861567266460327 / 10000000000000000000000000000000000000000) : ℝ) ((-377372274402321837214808196588334524203 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-377372274402321837274927861567266460327 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV1Interval.2 : ℝ) ≤ ((-377372274402321837214808196588334524203 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV1_exact_interval.1, manuscriptCase2Y4YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y4YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (0) (0) (1903396887835783614121 / 976562500000000000000) (0 / 1)

private theorem manuscriptCase2Y4YV2_arg_eq : barrierCase2Y4YV2LogArg = barrierComplex (43627937011 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y4YV2LogArg, Case2PointData.Y4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y4YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y4YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y4YV2Interval.1 : ℝ) (manuscriptCase2Y4YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y4YV2LogArg).re ∈ _
  rw [manuscriptCase2Y4YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y4YV2LogArg (0) (0) (1903396887835783614121 / 976562500000000000000) (43627937011 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (43627937011 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y4YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y4YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y4YV2_rounded_endpoints :
    (-16986882878393565730642140270005398889 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y4YV2Interval.1 ∧ manuscriptCase2Y4YV2Interval.2 ≤ (-84934414391967828648567462792803404643 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y4YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y4YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-16986882878393565730642140270005398889 / 2000000000000000000000000000000000000000) : ℝ) ((-84934414391967828648567462792803404643 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-16986882878393565730642140270005398889 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y4YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y4YV2Interval.2 : ℝ) ≤ ((-84934414391967828648567462792803404643 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y4YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y4YV2_exact_interval.1, manuscriptCase2Y4YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
