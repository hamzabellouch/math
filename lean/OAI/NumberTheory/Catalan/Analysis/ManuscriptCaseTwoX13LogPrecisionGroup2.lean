import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX13

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X13XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (1) (0) (336772200937154931601 / 312500000000000000000) (0 / 1)

private theorem manuscriptCase2X13XV0_arg_eq : barrierCase2X13XV0LogArg = barrierComplex (18351354199 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV0LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV0Interval.1 : ℝ) (manuscriptCase2X13XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X13XV0LogArg).re ∈ _
  rw [manuscriptCase2X13XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X13XV0LogArg (1) (0) (336772200937154931601 / 312500000000000000000) (18351354199 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (18351354199 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV0_rounded_endpoints :
    (583611287579719514673933967016511896113 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV0Interval.1 ∧ manuscriptCase2X13XV0Interval.2 ≤ (145902821894929878694141646878662313929 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((583611287579719514673933967016511896113 / 10000000000000000000000000000000000000000) : ℝ) ((145902821894929878694141646878662313929 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((583611287579719514673933967016511896113 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV0Interval.2 : ℝ) ≤ ((145902821894929878694141646878662313929 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV0_exact_interval.1, manuscriptCase2X13XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (1) (0) (2381836525971894384409 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X13XV1_arg_eq : barrierCase2X13XV1LogArg = barrierComplex (48804062597 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV1LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV1Interval.1 : ℝ) (manuscriptCase2X13XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X13XV1LogArg).re ∈ _
  rw [manuscriptCase2X13XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X13XV1LogArg (1) (0) (2381836525971894384409 / 1953125000000000000000) (48804062597 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (48804062597 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV1_rounded_endpoints :
    (19845250249504818359210242272888754361 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV1Interval.1 ∧ manuscriptCase2X13XV1Interval.2 ≤ (198452502495048183622162255218348947531 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((19845250249504818359210242272888754361 / 1000000000000000000000000000000000000000) : ℝ) ((198452502495048183622162255218348947531 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((19845250249504818359210242272888754361 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV1Interval.2 : ℝ) ≤ ((198452502495048183622162255218348947531 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV1_exact_interval.1, manuscriptCase2X13XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X13XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-3) (0) (3676615814170746723721 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X13XV2_arg_eq : barrierCase2X13XV2LogArg = barrierComplex (60635103811 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X13XV2LogArg, Case2PointData.X13, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X13XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X13XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X13XV2Interval.1 : ℝ) (manuscriptCase2X13XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X13XV2LogArg).re ∈ _
  rw [manuscriptCase2X13XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X13XV2LogArg (-3) (0) (3676615814170746723721 / 1953125000000000000000) (60635103811 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (60635103811 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X13XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X13XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X13XV2_rounded_endpoints :
    (-92072103509771073330661831324631641359 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X13XV2Interval.1 ∧ manuscriptCase2X13XV2Interval.2 ≤ (-92072103509771073304518465028245648239 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X13XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X13XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X13 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-92072103509771073330661831324631641359 / 5000000000000000000000000000000000000000) : ℝ) ((-92072103509771073304518465028245648239 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-92072103509771073330661831324631641359 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X13XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X13XV2Interval.2 : ℝ) ≤ ((-92072103509771073304518465028245648239 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X13XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X13XV2_exact_interval.1, manuscriptCase2X13XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
