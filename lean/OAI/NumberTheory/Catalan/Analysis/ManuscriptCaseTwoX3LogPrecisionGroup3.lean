import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX3

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X3XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (1) (0) (26173496590758023794849 / 20000000000000000000000) (0 / 1)

private theorem manuscriptCase2X3XV3_arg_eq : barrierCase2X3XV3LogArg = barrierComplex (161782250543 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV3LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV3Interval.1 : ℝ) (manuscriptCase2X3XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X3XV3LogArg).re ∈ _
  rw [manuscriptCase2X3XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X3XV3LogArg (1) (0) (26173496590758023794849 / 20000000000000000000000) (161782250543 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (161782250543 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV3_rounded_endpoints :
    (-237299705295286325724358229190058826913 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV3Interval.1 ∧ manuscriptCase2X3XV3Interval.2 ≤ (-237299705295286325691050634909131334341 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-237299705295286325724358229190058826913 / 10000000000000000000000000000000000000000) : ℝ) ((-237299705295286325691050634909131334341 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-237299705295286325724358229190058826913 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV3Interval.2 : ℝ) ≤ ((-237299705295286325691050634909131334341 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV3_exact_interval.1, manuscriptCase2X3XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (1) (0) (1050540500352652332388561 / 781250000000000000000000) (0 / 1)

private theorem manuscriptCase2X3XV4_arg_eq : barrierCase2X3XV4LogArg = barrierComplex (1024958779831 / 625000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV4LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV4Interval.1 : ℝ) (manuscriptCase2X3XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X3XV4LogArg).re ∈ _
  rw [manuscriptCase2X3XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X3XV4LogArg (1) (0) (1050540500352652332388561 / 781250000000000000000000) (1024958779831 / 625000000000) (0 / 1)
  have hratio : ((0 / 1) / (1024958779831 / 625000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV4_rounded_endpoints :
    (574699137371820296601970159724202533083 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV4Interval.1 ∧ manuscriptCase2X3XV4Interval.2 ≤ (114939827474364059336084345057394229471 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((574699137371820296601970159724202533083 / 10000000000000000000000000000000000000000) : ℝ) ((114939827474364059336084345057394229471 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((574699137371820296601970159724202533083 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV4Interval.2 : ℝ) ≤ ((114939827474364059336084345057394229471 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV4_exact_interval.1, manuscriptCase2X3XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (1) (78582348197679651501289 / 62500000000000000000000) (-123183801517 / 376816198483)

private theorem manuscriptCase2X3XV5_arg_eq : barrierCase2X3XV5LogArg = barrierComplex (1 / 1) (126816198483 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV5LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV5Interval.1 : ℝ) (manuscriptCase2X3XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X3XV5LogArg).re ∈ _
  rw [manuscriptCase2X3XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X3XV5LogArg (0) (1) (78582348197679651501289 / 62500000000000000000000) (376816198483 / 250000000000) (-123183801517 / 250000000000)
  have hratio : ((-123183801517 / 250000000000) / (376816198483 / 250000000000) : ℚ) = (-123183801517 / 376816198483) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV5_rounded_endpoints :
    (-149305289963133575331325415542692093427 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV5Interval.1 ∧ manuscriptCase2X3XV5Interval.2 ≤ (-373263224907833903482775632231094380979 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-149305289963133575331325415542692093427 / 2000000000000000000000000000000000000000) : ℝ) ((-373263224907833903482775632231094380979 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-149305289963133575331325415542692093427 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV5Interval.2 : ℝ) ≤ ((-373263224907833903482775632231094380979 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV5_exact_interval.1, manuscriptCase2X3XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
