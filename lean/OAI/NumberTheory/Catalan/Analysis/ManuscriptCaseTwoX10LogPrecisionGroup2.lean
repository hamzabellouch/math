import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX10

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X10XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (0) (0) (212356245929640416041 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2X10XV0_arg_eq : barrierCase2X10XV0LogArg = barrierComplex (14572448179 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV0LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV0Interval.1 : ℝ) (manuscriptCase2X10XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X10XV0LogArg).re ∈ _
  rw [manuscriptCase2X10XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X10XV0LogArg (0) (0) (212356245929640416041 / 156250000000000000000) (14572448179 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (14572448179 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV0_rounded_endpoints :
    (58290490511991522372608724638870245097 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X10XV0Interval.1 ∧ manuscriptCase2X10XV0Interval.2 ≤ (23316196204796608949043489855550466111 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((58290490511991522372608724638870245097 / 2500000000000000000000000000000000000000) : ℝ) ((23316196204796608949043489855550466111 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((58290490511991522372608724638870245097 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV0Interval.2 : ℝ) ≤ ((23316196204796608949043489855550466111 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV0_exact_interval.1, manuscriptCase2X10XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (0) (0) (1403801906654263744369 / 976562500000000000000) (0 / 1)

private theorem manuscriptCase2X10XV1_arg_eq : barrierCase2X10XV1LogArg = barrierComplex (37467344537 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV1LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV1Interval.1 : ℝ) (manuscriptCase2X10XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X10XV1LogArg).re ∈ _
  rw [manuscriptCase2X10XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X10XV1LogArg (0) (0) (1403801906654263744369 / 976562500000000000000) (37467344537 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (37467344537 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV1_rounded_endpoints :
    (10096946188350636745129029762828732761 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X10XV1Interval.1 ∧ manuscriptCase2X10XV1Interval.2 ≤ (80775569506805093961032238105745680557 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((10096946188350636745129029762828732761 / 1250000000000000000000000000000000000000) : ℝ) ((80775569506805093961032238105745680557 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((10096946188350636745129029762828732761 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV1Interval.2 : ℝ) ≤ ((80775569506805093961032238105745680557 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV1_exact_interval.1, manuscriptCase2X10XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-1) (0) (10445467523761490340961 / 7812500000000000000000) (0 / 1)

private theorem manuscriptCase2X10XV2_arg_eq : barrierCase2X10XV2LogArg = barrierComplex (102203070031 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XV2LogArg, Case2PointData.X10, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XV2Interval.1 : ℝ) (manuscriptCase2X10XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X10XV2LogArg).re ∈ _
  rw [manuscriptCase2X10XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X10XV2LogArg (-1) (0) (10445467523761490340961 / 7812500000000000000000) (102203070031 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (102203070031 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XV2_rounded_endpoints :
    (-51252103038255268858839093710065412249 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X10XV2Interval.1 ∧ manuscriptCase2X10XV2Interval.2 ≤ (-51252103038255268841651302386507499241 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X10 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-51252103038255268858839093710065412249 / 10000000000000000000000000000000000000000) : ℝ) ((-51252103038255268841651302386507499241 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-51252103038255268858839093710065412249 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XV2Interval.2 : ℝ) ≤ ((-51252103038255268841651302386507499241 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XV2_exact_interval.1, manuscriptCase2X10XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
