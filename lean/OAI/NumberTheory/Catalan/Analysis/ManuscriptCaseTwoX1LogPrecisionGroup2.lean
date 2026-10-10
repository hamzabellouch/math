import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX1

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X1XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-4) (0) (791069016156248449 / 610351562500000000) (0 / 1)

private theorem manuscriptCase2X1XV0_arg_eq : barrierCase2X1XV0LogArg = barrierComplex (889420607 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV0LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV0Interval.1 : ℝ) (manuscriptCase2X1XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X1XV0LogArg).re ∈ _
  rw [manuscriptCase2X1XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X1XV0LogArg (-4) (0) (791069016156248449 / 610351562500000000) (889420607 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (889420607 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV0_rounded_endpoints :
    (-477490552811742578761174112627502026951 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X1XV0Interval.1 ∧ manuscriptCase2X1XV0Interval.2 ≤ (-76398488449878812585366638740698344739 / 400000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-477490552811742578761174112627502026951 / 2500000000000000000000000000000000000000) : ℝ) ((-76398488449878812585366638740698344739 / 400000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-477490552811742578761174112627502026951 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV0Interval.2 : ℝ) ≤ ((-76398488449878812585366638740698344739 / 400000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV0_exact_interval.1, manuscriptCase2X1XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-6) (0) (1222709204781236041 / 953674316406250000) (0 / 1)

private theorem manuscriptCase2X1XV1_arg_eq : barrierCase2X1XV1LogArg = barrierComplex (1105761821 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV1LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV1Interval.1 : ℝ) (manuscriptCase2X1XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X1XV1LogArg).re ∈ _
  rw [manuscriptCase2X1XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X1XV1LogArg (-6) (0) (1222709204781236041 / 953674316406250000) (1105761821 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (1105761821 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV1_rounded_endpoints :
    (-108798089914608079980093455110306110377 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X1XV1Interval.1 ∧ manuscriptCase2X1XV1Interval.2 ≤ (-13599761239326009994693572592901257131 / 156250000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-108798089914608079980093455110306110377 / 1250000000000000000000000000000000000000) : ℝ) ((-13599761239326009994693572592901257131 / 156250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-108798089914608079980093455110306110377 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV1Interval.2 : ℝ) ≤ ((-13599761239326009994693572592901257131 / 156250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV1_exact_interval.1, manuscriptCase2X1XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X1XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (1) (0) (3118258974598656062329 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X1XV2_arg_eq : barrierCase2X1XV2LogArg = barrierComplex (55841373323 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X1XV2LogArg, Case2PointData.X1, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X1XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X1XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X1XV2Interval.1 : ℝ) (manuscriptCase2X1XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X1XV2LogArg).re ∈ _
  rw [manuscriptCase2X1XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X1XV2LogArg (1) (0) (3118258974598656062329 / 1953125000000000000000) (55841373323 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (55841373323 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X1XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X1XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X1XV2_rounded_endpoints :
    (29551850646983567683831102418077092033 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X1XV2Interval.1 ∧ manuscriptCase2X1XV2Interval.2 ≤ (73879626617458919218171660146176267377 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X1XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X1XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X1 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((29551850646983567683831102418077092033 / 2000000000000000000000000000000000000000) : ℝ) ((73879626617458919218171660146176267377 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((29551850646983567683831102418077092033 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X1XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X1XV2Interval.2 : ℝ) ≤ ((73879626617458919218171660146176267377 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X1XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X1XV2_exact_interval.1, manuscriptCase2X1XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
