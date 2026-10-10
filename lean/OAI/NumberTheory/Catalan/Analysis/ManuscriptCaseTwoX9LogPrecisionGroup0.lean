import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX9Group0

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X9XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (1) (0) (5344113155196336409729 / 5000000000000000000000) (0 / 1)

private theorem manuscriptCase2X9XP0_arg_eq : barrierCase2X9XP0LogArg = barrierComplex (73103441473 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XP0LogArg, Case2PointData.X9, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XP0Interval.1 : ℝ) (manuscriptCase2X9XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X9XP0LogArg).re ∈ _
  rw [manuscriptCase2X9XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X9XP0LogArg (1) (0) (5344113155196336409729 / 5000000000000000000000) (73103441473 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (73103441473 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XP0_rounded_endpoints :
    (-709446754098124664862337048130012034123 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XP0Interval.1 ∧ manuscriptCase2X9XP0Interval.2 ≤ (-7094467540981246647362213174968795877 / 100000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-709446754098124664862337048130012034123 / 10000000000000000000000000000000000000000) : ℝ) ((-7094467540981246647362213174968795877 / 100000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-709446754098124664862337048130012034123 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XP0Interval.2 : ℝ) ≤ ((-7094467540981246647362213174968795877 / 100000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XP0_exact_interval.1, manuscriptCase2X9XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (1) (0) (39779991575210253214849 / 31250000000000000000000) (0 / 1)

private theorem manuscriptCase2X9XP1_arg_eq : barrierCase2X9XP1LogArg = barrierComplex (199449220543 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XP1LogArg, Case2PointData.X9, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XP1Interval.1 : ℝ) (manuscriptCase2X9XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X9XP1LogArg).re ∈ _
  rw [manuscriptCase2X9XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X9XP1LogArg (1) (0) (39779991575210253214849 / 31250000000000000000000) (199449220543 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (199449220543 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XP1_rounded_endpoints :
    (-5003056853765027647547442910066491877 / 250000000000000000000000000000000000000) ≤ manuscriptCase2X9XP1Interval.1 ∧ manuscriptCase2X9XP1Interval.2 ≤ (-100061137075300552936488325974338209709 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-5003056853765027647547442910066491877 / 250000000000000000000000000000000000000) : ℝ) ((-100061137075300552936488325974338209709 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-5003056853765027647547442910066491877 / 250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XP1Interval.2 : ℝ) ≤ ((-100061137075300552936488325974338209709 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XP1_exact_interval.1, manuscriptCase2X9XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X9XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (191311594592153059089 / 156250000000000000000) (2462727261 / 6037272739)

private theorem manuscriptCase2X9XP2_arg_eq : barrierCase2X9XP2LogArg = barrierComplex (51 / 100) (-5361818217 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X9XP2LogArg, Case2PointData.X9, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X9XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X9XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X9XP2Interval.1 : ℝ) (manuscriptCase2X9XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X9XP2LogArg).re ∈ _
  rw [manuscriptCase2X9XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X9XP2LogArg (-2) (-1) (191311594592153059089 / 156250000000000000000) (18111818217 / 25000000000) (7388181783 / 25000000000)
  have hratio : ((7388181783 / 25000000000) / (18111818217 / 25000000000) : ℚ) = (2462727261 / 6037272739) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X9XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X9XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X9XP2_rounded_endpoints :
    (5193334238324059438109875960598002349343 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X9XP2Interval.1 ∧ manuscriptCase2X9XP2Interval.2 ≤ (1298333559581014888670561924485459855277 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X9XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X9XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X9 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((5193334238324059438109875960598002349343 / 10000000000000000000000000000000000000000) : ℝ) ((1298333559581014888670561924485459855277 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((5193334238324059438109875960598002349343 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X9XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X9XP2Interval.2 : ℝ) ≤ ((1298333559581014888670561924485459855277 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X9XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X9XP2_exact_interval.1, manuscriptCase2X9XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
