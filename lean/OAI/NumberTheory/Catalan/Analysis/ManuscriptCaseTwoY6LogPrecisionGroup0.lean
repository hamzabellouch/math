import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY6

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y6YV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-15199211 / 100000000) (0 / 1) (2) (0) (3318180608477487769 / 2441406250000000000) (0 / 1)

private theorem manuscriptCase2Y6YV0_arg_eq : barrierCase2Y6YV0LogArg = barrierComplex (1821587387 / 781250000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV0LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV0_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) = barrierComplex (-15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV0_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV0Interval.1 : ℝ) (manuscriptCase2Y6YV0Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 0 (0, 0)).2) * Complex.log barrierCase2Y6YV0LogArg).re ∈ _
  rw [manuscriptCase2Y6YV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-15199211 / 100000000) (0 / 1)
    barrierCase2Y6YV0LogArg (2) (0) (3318180608477487769 / 2441406250000000000) (1821587387 / 781250000) (0 / 1)
  have hratio : ((0 / 1) / (1821587387 / 781250000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV0_rounded_endpoints :
    (-160839644732298185815471392184554454267 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV0Interval.1 ∧ manuscriptCase2Y6YV0Interval.2 ≤ (-1286717157858385486318505896480137137073 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV0_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-160839644732298185815471392184554454267 / 1250000000000000000000000000000000000000) : ℝ) ((-1286717157858385486318505896480137137073 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-160839644732298185815471392184554454267 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV0_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV0Interval.2 : ℝ) ≤ ((-1286717157858385486318505896480137137073 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV0_exact_interval.1, manuscriptCase2Y6YV0_exact_interval.2.trans hhi⟩

def manuscriptCase2Y6YV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2225831 / 50000000) (0 / 1) (2) (0) (28881350225241139921 / 15258789062500000000) (0 / 1)

private theorem manuscriptCase2Y6YV1_arg_eq : barrierCase2Y6YV1LogArg = barrierComplex (5374137161 / 1953125000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV1LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV1_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) = barrierComplex (-2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV1_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV1Interval.1 : ℝ) (manuscriptCase2Y6YV1Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 1 (0, 0)).2) * Complex.log barrierCase2Y6YV1LogArg).re ∈ _
  rw [manuscriptCase2Y6YV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2225831 / 50000000) (0 / 1)
    barrierCase2Y6YV1LogArg (2) (0) (28881350225241139921 / 15258789062500000000) (5374137161 / 1953125000) (0 / 1)
  have hratio : ((0 / 1) / (5374137161 / 1953125000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV1_rounded_endpoints :
    (-450582705872954602400427874667382631789 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV1Interval.1 ∧ manuscriptCase2Y6YV1Interval.2 ≤ (-90116541174590920467720018400304055391 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV1_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-450582705872954602400427874667382631789 / 10000000000000000000000000000000000000000) : ℝ) ((-90116541174590920467720018400304055391 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-450582705872954602400427874667382631789 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV1_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV1Interval.2 : ℝ) ≤ ((-90116541174590920467720018400304055391 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV1_exact_interval.1, manuscriptCase2Y6YV1_exact_interval.2.trans hhi⟩

def manuscriptCase2Y6YV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1272699 / 50000000) (0 / 1) (0) (0) (62707215156263520049 / 61035156250000000000) (0 / 1)

private theorem manuscriptCase2Y6YV2_arg_eq : barrierCase2Y6YV2LogArg = barrierComplex (7918788743 / 7812500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y6YV2LogArg, Case2PointData.Y6, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y6YV2_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) = barrierComplex (-1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y6YV2_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2Y6YV2Interval.1 : ℝ) (manuscriptCase2Y6YV2Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 2 (0, 0)).2) * Complex.log barrierCase2Y6YV2LogArg).re ∈ _
  rw [manuscriptCase2Y6YV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1272699 / 50000000) (0 / 1)
    barrierCase2Y6YV2LogArg (0) (0) (62707215156263520049 / 61035156250000000000) (7918788743 / 7812500000) (0 / 1)
  have hratio : ((0 / 1) / (7918788743 / 7812500000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y6YV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y6YV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y6YV2_rounded_endpoints :
    (-859914515784964007556791499536267547 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y6YV2Interval.1 ∧ manuscriptCase2Y6YV2Interval.2 ≤ (-3439658063139856030227165998145070187 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y6YV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y6YV2_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y6 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-859914515784964007556791499536267547 / 2500000000000000000000000000000000000000) : ℝ) ((-3439658063139856030227165998145070187 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-859914515784964007556791499536267547 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y6YV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV2_rounded_endpoints.1
  have hhi : (manuscriptCase2Y6YV2Interval.2 : ℝ) ≤ ((-3439658063139856030227165998145070187 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y6YV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y6YV2_exact_interval.1, manuscriptCase2Y6YV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
