import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX15Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X15XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (-4) (0) (219266264058232578889 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2X15XP0_arg_eq : barrierCase2X15XP0LogArg = barrierComplex (14807642083 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XP0LogArg, Case2PointData.X15, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XP0Interval.1 : ℝ) (manuscriptCase2X15XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X15XP0LogArg).re ∈ _
  rw [manuscriptCase2X15XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X15XP0LogArg (-4) (0) (219266264058232578889 / 156250000000000000000) (14807642083 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (14807642083 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XP0_rounded_endpoints :
    (1136377174339079343555801996561373222161 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X15XP0Interval.1 ∧ manuscriptCase2X15XP0Interval.2 ≤ (90910173947126347504642676626254305877 / 400000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((1136377174339079343555801996561373222161 / 5000000000000000000000000000000000000000) : ℝ) ((90910173947126347504642676626254305877 / 400000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1136377174339079343555801996561373222161 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XP0Interval.2 : ℝ) ≤ ((90910173947126347504642676626254305877 / 400000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XP0_exact_interval.1, manuscriptCase2X15XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (-4) (0) (1465242111724879988809 / 976562500000000000000) (0 / 1)

private theorem manuscriptCase2X15XP1_arg_eq : barrierCase2X15XP1LogArg = barrierComplex (38278481053 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XP1LogArg, Case2PointData.X15, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XP1Interval.1 : ℝ) (manuscriptCase2X15XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X15XP1LogArg).re ∈ _
  rw [manuscriptCase2X15XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X15XP1LogArg (-4) (0) (1465242111724879988809 / 976562500000000000000) (38278481053 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (38278481053 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XP1_rounded_endpoints :
    (506863422328004014597086730075653761367 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X15XP1Interval.1 ∧ manuscriptCase2X15XP1Interval.2 ≤ (25343171116400200735638549403068466591 / 500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((506863422328004014597086730075653761367 / 10000000000000000000000000000000000000000) : ℝ) ((25343171116400200735638549403068466591 / 500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((506863422328004014597086730075653761367 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XP1Interval.2 : ℝ) ≤ ((25343171116400200735638549403068466591 / 500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XP1_exact_interval.1, manuscriptCase2X15XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X15XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (0) (-2) (1024922747310770402649 / 625000000000000000000) (4250000000 / 9788656969)

private theorem manuscriptCase2X15XP2_arg_eq : barrierCase2X15XP2LogArg = barrierComplex (51 / 100) (-29365970907 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X15XP2LogArg, Case2PointData.X15, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X15XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X15XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X15XP2Interval.1 : ℝ) (manuscriptCase2X15XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X15XP2LogArg).re ∈ _
  rw [manuscriptCase2X15XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X15XP2LogArg (0) (-2) (1024922747310770402649 / 625000000000000000000) (29365970907 / 12500000000) (51 / 50)
  have hratio : ((51 / 50) / (29365970907 / 12500000000) : ℚ) = (4250000000 / 9788656969) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X15XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X15XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X15XP2_rounded_endpoints :
    (1032959283877478539014535548201460456787 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X15XP2Interval.1 ∧ manuscriptCase2X15XP2Interval.2 ≤ (413183713550991461897500161494840544269 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X15XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X15XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X15 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((1032959283877478539014535548201460456787 / 5000000000000000000000000000000000000000) : ℝ) ((413183713550991461897500161494840544269 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((1032959283877478539014535548201460456787 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X15XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X15XP2Interval.2 : ℝ) ≤ ((413183713550991461897500161494840544269 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X15XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X15XP2_exact_interval.1, manuscriptCase2X15XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
