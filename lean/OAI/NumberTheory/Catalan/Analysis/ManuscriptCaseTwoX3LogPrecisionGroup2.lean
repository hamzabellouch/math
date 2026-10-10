import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX3

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X3XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-3) (0) (8989818499156575609 / 4882812500000000000) (0 / 1)

private theorem manuscriptCase2X3XV0_arg_eq : barrierCase2X3XV0LogArg = barrierComplex (2998302603 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV0LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV0Interval.1 : ℝ) (manuscriptCase2X3XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XV0LogArg).re ∈ _
  rw [manuscriptCase2X3XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X3XV0LogArg (-3) (0) (8989818499156575609 / 4882812500000000000) (2998302603 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (2998302603 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV0_rounded_endpoints :
    (-1116435449169292967287215172723285108487 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV0Interval.1 ∧ manuscriptCase2X3XV0Interval.2 ≤ (-279108862292323241744518902846669578217 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1116435449169292967287215172723285108487 / 10000000000000000000000000000000000000000) : ℝ) ((-279108862292323241744518902846669578217 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1116435449169292967287215172723285108487 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV0Interval.2 : ℝ) ≤ ((-279108862292323241744518902846669578217 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV0_exact_interval.1, manuscriptCase2X3XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-3) (0) (34455817686159180481 / 30517578125000000000) (0 / 1)

private theorem manuscriptCase2X3XV1_arg_eq : barrierCase2X3XV1LogArg = barrierComplex (5869907809 / 15625000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV1LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV1Interval.1 : ℝ) (manuscriptCase2X3XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XV1LogArg).re ∈ _
  rw [manuscriptCase2X3XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X3XV1LogArg (-3) (0) (34455817686159180481 / 30517578125000000000) (5869907809 / 15625000000) (0 / 1)
  have hratio : ((0 / 1) / (5869907809 / 15625000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV1_rounded_endpoints :
    (-43583251930300659558661096057611730101 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV1Interval.1 ∧ manuscriptCase2X3XV1Interval.2 ≤ (-108958129825751648874107865776933272313 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-43583251930300659558661096057611730101 / 1000000000000000000000000000000000000000) : ℝ) ((-108958129825751648874107865776933272313 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-43583251930300659558661096057611730101 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV1Interval.2 : ℝ) ≤ ((-108958129825751648874107865776933272313 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV1_exact_interval.1, manuscriptCase2X3XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (1) (0) (9656731772235445648689 / 7812500000000000000000) (0 / 1)

private theorem manuscriptCase2X3XV2_arg_eq : barrierCase2X3XV2LogArg = barrierComplex (98268671367 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV2LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV2Interval.1 : ℝ) (manuscriptCase2X3XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XV2LogArg).re ∈ _
  rw [manuscriptCase2X3XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X3XV2LogArg (1) (0) (9656731772235445648689 / 7812500000000000000000) (98268671367 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (98268671367 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV2_rounded_endpoints :
    (115189114087417549113267269008022476363 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV2Interval.1 ∧ manuscriptCase2X3XV2Interval.2 ≤ (23037822817483509826091012066315970611 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((115189114087417549113267269008022476363 / 10000000000000000000000000000000000000000) : ℝ) ((23037822817483509826091012066315970611 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((115189114087417549113267269008022476363 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV2Interval.2 : ℝ) ≤ ((23037822817483509826091012066315970611 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV2_exact_interval.1, manuscriptCase2X3XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
