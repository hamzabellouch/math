import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY11

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y11YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (6142814676039312441 / 4882812500000000000) (0 / 1)

private theorem manuscriptCase2Y11YV0_arg_eq : barrierCase2Y11YV0LogArg = barrierComplex (2478470229 / 781250000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV0LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV0Interval.1 : ℝ) (manuscriptCase2Y11YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y11YV0LogArg).re ∈ _
  rw [manuscriptCase2Y11YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y11YV0LogArg (3) (0) (6142814676039312441 / 4882812500000000000) (2478470229 / 781250000) (0 / 1)
  have hratio : ((0 / 1) / (2478470229 / 781250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV0_rounded_endpoints :
    (-1754751348872015482015568087765836623319 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV0Interval.1 ∧ manuscriptCase2Y11YV0Interval.2 ≤ (-175475134887201548170767022627142454393 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1754751348872015482015568087765836623319 / 10000000000000000000000000000000000000000) : ℝ) ((-175475134887201548170767022627142454393 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1754751348872015482015568087765836623319 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV0Interval.2 : ℝ) ≤ ((-175475134887201548170767022627142454393 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV0_exact_interval.1, manuscriptCase2Y11YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y11YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (53945876787960061969 / 30517578125000000000) (0 / 1)

private theorem manuscriptCase2Y11YV1_arg_eq : barrierCase2Y11YV1LogArg = barrierComplex (7344785687 / 1953125000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV1LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV1Interval.1 : ℝ) (manuscriptCase2Y11YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y11YV1LogArg).re ∈ _
  rw [manuscriptCase2Y11YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y11YV1LogArg (3) (0) (53945876787960061969 / 30517578125000000000) (7344785687 / 1953125000) (0 / 1)
  have hratio : ((0 / 1) / (7344785687 / 1953125000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV1_rounded_endpoints :
    (-589649331712059132600948633852023540953 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV1Interval.1 ∧ manuscriptCase2Y11YV1Interval.2 ≤ (-294824665856029566255368434992570754919 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-589649331712059132600948633852023540953 / 10000000000000000000000000000000000000000) : ℝ) ((-294824665856029566255368434992570754919 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-589649331712059132600948633852023540953 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV1Interval.2 : ℝ) ≤ ((-294824665856029566255368434992570754919 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV1_exact_interval.1, manuscriptCase2Y11YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y11YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-7) (0) (480356394669305361 / 476837158203125000) (0 / 1)

private theorem manuscriptCase2Y11YV2_arg_eq : barrierCase2Y11YV2LogArg = barrierComplex (693077481 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y11YV2LogArg, Case2PointData.Y11, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y11YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y11YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y11YV2Interval.1 : ℝ) (manuscriptCase2Y11YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y11YV2LogArg).re ∈ _
  rw [manuscriptCase2Y11YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y11YV2LogArg (-7) (0) (480356394669305361 / 476837158203125000) (693077481 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (693077481 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y11YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y11YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y11YV2_rounded_endpoints :
    (616581556281151649226039151836875491491 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y11YV2Interval.1 ∧ manuscriptCase2Y11YV2Interval.2 ≤ (308290778140575824673176845550888564147 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y11YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y11YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y11 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((616581556281151649226039151836875491491 / 10000000000000000000000000000000000000000) : ℝ) ((308290778140575824673176845550888564147 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((616581556281151649226039151836875491491 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y11YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y11YV2Interval.2 : ℝ) ≤ ((308290778140575824673176845550888564147 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y11YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y11YV2_exact_interval.1, manuscriptCase2Y11YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
