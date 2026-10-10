import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY17

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y17YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (3) (0) (5041 / 5000) (0 / 1)

private theorem manuscriptCase2Y17YV0_arg_eq : barrierCase2Y17YV0LogArg = barrierComplex (71 / 25) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV0LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV0Interval.1 : ℝ) (manuscriptCase2Y17YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y17YV0LogArg).re ∈ _
  rw [manuscriptCase2Y17YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y17YV0LogArg (3) (0) (5041 / 5000) (71 / 25) (0 / 1)
  have hratio : ((0 / 1) / (71 / 25) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV0_rounded_endpoints :
    (-198312475395427230361097708459784145023 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV0Interval.1 ∧ manuscriptCase2Y17YV0Interval.2 ≤ (-49578118848856807580652618943245658793 / 312500000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-198312475395427230361097708459784145023 / 1250000000000000000000000000000000000000) : ℝ) ((-49578118848856807580652618943245658793 / 312500000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-198312475395427230361097708459784145023 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV0Interval.2 : ℝ) ≤ ((-49578118848856807580652618943245658793 / 312500000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV0_exact_interval.1, manuscriptCase2Y17YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y17YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (3) (0) (4414201 / 3125000) (0 / 1)

private theorem manuscriptCase2Y17YV1_arg_eq : barrierCase2Y17YV1LogArg = barrierComplex (2101 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV1LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV1Interval.1 : ℝ) (manuscriptCase2Y17YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y17YV1LogArg).re ∈ _
  rw [manuscriptCase2Y17YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y17YV1LogArg (3) (0) (4414201 / 3125000) (2101 / 625) (0 / 1)
  have hratio : ((0 / 1) / (2101 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV1_rounded_endpoints :
    (-539727091457220767877268324001947632739 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV1Interval.1 ∧ manuscriptCase2Y17YV1Interval.2 ≤ (-539727091457220767787088826533045771817 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-539727091457220767877268324001947632739 / 10000000000000000000000000000000000000000) : ℝ) ((-539727091457220767787088826533045771817 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-539727091457220767877268324001947632739 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV1Interval.2 : ℝ) ≤ ((-539727091457220767787088826533045771817 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV1_exact_interval.1, manuscriptCase2Y17YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y17YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (-3) (0) (645248 / 390625) (0 / 1)

private theorem manuscriptCase2Y17YV2_arg_eq : barrierCase2Y17YV2LogArg = barrierComplex (284 / 625) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y17YV2LogArg, Case2PointData.Y17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y17YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y17YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y17YV2Interval.1 : ℝ) (manuscriptCase2Y17YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y17YV2LogArg).re ∈ _
  rw [manuscriptCase2Y17YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y17YV2LogArg (-3) (0) (645248 / 390625) (284 / 625) (0 / 1)
  have hratio : ((0 / 1) / (284 / 625) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y17YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y17YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y17YV2_rounded_endpoints :
    (200775244586867936849856787471306182269 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y17YV2Interval.1 ∧ manuscriptCase2Y17YV2Interval.2 ≤ (5019381114671698422535509217265012423 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y17YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y17YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y17 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((200775244586867936849856787471306182269 / 10000000000000000000000000000000000000000) : ℝ) ((5019381114671698422535509217265012423 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((200775244586867936849856787471306182269 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y17YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y17YV2Interval.2 : ℝ) ≤ ((5019381114671698422535509217265012423 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y17YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y17YV2_exact_interval.1, manuscriptCase2Y17YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
