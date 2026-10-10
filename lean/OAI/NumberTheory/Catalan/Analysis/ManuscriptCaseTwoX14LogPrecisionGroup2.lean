import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX14

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X14XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (1) (0) (390814574540776060249 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2X14XV0_arg_eq : barrierCase2X14XV0LogArg = barrierComplex (19769030693 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV0LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV0Interval.1 : ℝ) (manuscriptCase2X14XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X14XV0LogArg).re ∈ _
  rw [manuscriptCase2X14XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X14XV0LogArg (1) (0) (390814574540776060249 / 312500000000000000000) (19769030693 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (19769030693 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV0_rounded_endpoints :
    (696713536169491350858455460812491704637 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X14XV0Interval.1 ∧ manuscriptCase2X14XV0Interval.2 ≤ (696713536169491350961088081310629064463 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((696713536169491350858455460812491704637 / 10000000000000000000000000000000000000000) : ℝ) ((696713536169491350961088081310629064463 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((696713536169491350858455460812491704637 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV0Interval.2 : ℝ) ≤ ((696713536169491350961088081310629064463 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV0_exact_interval.1, manuscriptCase2X14XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (1) (0) (2815055019879484542241 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X14XV1_arg_eq : barrierCase2X14XV1LogArg = barrierComplex (53057092079 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV1LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV1Interval.1 : ℝ) (manuscriptCase2X14XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X14XV1LogArg).re ∈ _
  rw [manuscriptCase2X14XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X14XV1LogArg (1) (0) (2815055019879484542241 / 1953125000000000000000) (53057092079 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (53057092079 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV1_rounded_endpoints :
    (117824178491837300414428590648435097631 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X14XV1Interval.1 ∧ manuscriptCase2X14XV1Interval.2 ≤ (117824178491837300429458506895194113991 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((117824178491837300414428590648435097631 / 5000000000000000000000000000000000000000) : ℝ) ((117824178491837300429458506895194113991 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((117824178491837300414428590648435097631 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV1Interval.2 : ℝ) ≤ ((117824178491837300429458506895194113991 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV1_exact_interval.1, manuscriptCase2X14XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-3) (0) (2028661267358903290129 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X14XV2_arg_eq : barrierCase2X14XV2LogArg = barrierComplex (45040662377 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV2LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV2Interval.1 : ℝ) (manuscriptCase2X14XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X14XV2LogArg).re ∈ _
  rw [manuscriptCase2X14XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X14XV2LogArg (-3) (0) (2028661267358903290129 / 1953125000000000000000) (45040662377 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (45040662377 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV2_rounded_endpoints :
    (-129910501887564853387238298136042642909 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X14XV2Interval.1 ∧ manuscriptCase2X14XV2Interval.2 ≤ (-259821003775129706722913222301413155759 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-129910501887564853387238298136042642909 / 5000000000000000000000000000000000000000) : ℝ) ((-259821003775129706722913222301413155759 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-129910501887564853387238298136042642909 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV2Interval.2 : ℝ) ≤ ((-259821003775129706722913222301413155759 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV2_exact_interval.1, manuscriptCase2X14XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
