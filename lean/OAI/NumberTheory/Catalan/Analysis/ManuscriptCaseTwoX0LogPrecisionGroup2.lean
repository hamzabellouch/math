import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X0XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-5) (0) (525223010738080369 / 305175781250000000) (0 / 1)

private theorem manuscriptCase2X0XV0_arg_eq : barrierCase2X0XV0LogArg = barrierComplex (724722713 / 3125000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV0LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV0Interval.1 : ℝ) (manuscriptCase2X0XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X0XV0LogArg).re ∈ _
  rw [manuscriptCase2X0XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X0XV0LogArg (-5) (0) (525223010738080369 / 305175781250000000) (724722713 / 3125000000) (0 / 1)
  have hratio : ((0 / 1) / (724722713 / 3125000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV0_rounded_endpoints :
    (-22212133723635100766269959189 / 100000000000000000000000000000) ≤ manuscriptCase2X0XV0Interval.1 ∧ manuscriptCase2X0XV0Interval.2 ≤ (-222121337236351007611381264579 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-22212133723635100766269959189 / 100000000000000000000000000000) : ℝ) ((-222121337236351007611381264579 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-22212133723635100766269959189 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV0Interval.2 : ℝ) ≤ ((-222121337236351007611381264579 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV0_exact_interval.1, manuscriptCase2X0XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-8) (0) (374137912267723321 / 238418579101562500) (0 / 1)

private theorem manuscriptCase2X0XV1_arg_eq : barrierCase2X0XV1LogArg = barrierComplex (611668139 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV1LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV1Interval.1 : ℝ) (manuscriptCase2X0XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X0XV1LogArg).re ∈ _
  rw [manuscriptCase2X0XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X0XV1LogArg (-8) (0) (374137912267723321 / 238418579101562500) (611668139 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (611668139 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV1_rounded_endpoints :
    (-11339675944054200195960309293 / 100000000000000000000000000000) ≤ manuscriptCase2X0XV1Interval.1 ∧ manuscriptCase2X0XV1Interval.2 ≤ (-113396759440542001935555226169 / 1000000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-11339675944054200195960309293 / 100000000000000000000000000000) : ℝ) ((-113396759440542001935555226169 / 1000000000000000000000000000000) : ℝ) := by
  have hlo : ((-11339675944054200195960309293 / 100000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV1Interval.2 : ℝ) ≤ ((-113396759440542001935555226169 / 1000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV1_exact_interval.1, manuscriptCase2X0XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X0XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (1) (0) (3323874192405557724649 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X0XV2_arg_eq : barrierCase2X0XV2LogArg = barrierComplex (57653050157 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X0XV2LogArg, Case2PointData.X0, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X0XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X0XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X0XV2Interval.1 : ℝ) (manuscriptCase2X0XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X0XV2LogArg).re ∈ _
  rw [manuscriptCase2X0XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X0XV2LogArg (1) (0) (3323874192405557724649 / 1953125000000000000000) (57653050157 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (57653050157 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X0XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X0XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X0XV2_rounded_endpoints :
    (3117724515887614249246260421 / 200000000000000000000000000000) ≤ manuscriptCase2X0XV2Interval.1 ∧ manuscriptCase2X0XV2Interval.2 ≤ (1558862257943807124795024231 / 100000000000000000000000000000) := by
  simp only [manuscriptCase2X0XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X0XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X0 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((3117724515887614249246260421 / 200000000000000000000000000000) : ℝ) ((1558862257943807124795024231 / 100000000000000000000000000000) : ℝ) := by
  have hlo : ((3117724515887614249246260421 / 200000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X0XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X0XV2Interval.2 : ℝ) ≤ ((1558862257943807124795024231 / 100000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X0XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X0XV2_exact_interval.1, manuscriptCase2X0XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
