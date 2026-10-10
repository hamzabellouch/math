import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX4

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X4XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (-2) (0) (2139863379026332969 / 1562500000000000000) (0 / 1)

private theorem manuscriptCase2X4XV0_arg_eq : barrierCase2X4XV0LogArg = barrierComplex (1462827187 / 2500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV0LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV0Interval.1 : ℝ) (manuscriptCase2X4XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X4XV0LogArg).re ∈ _
  rw [manuscriptCase2X4XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X4XV0LogArg (-2) (0) (2139863379026332969 / 1562500000000000000) (1462827187 / 2500000000) (0 / 1)
  have hratio : ((0 / 1) / (1462827187 / 2500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV0_rounded_endpoints :
    (-814555719462612411491506882955700870387 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XV0Interval.1 ∧ manuscriptCase2X4XV0Interval.2 ≤ (-814555719462612411286241641959368046857 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-814555719462612411491506882955700870387 / 10000000000000000000000000000000000000000) : ℝ) ((-814555719462612411286241641959368046857 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-814555719462612411491506882955700870387 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV0Interval.2 : ℝ) ≤ ((-814555719462612411286241641959368046857 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV0_exact_interval.1, manuscriptCase2X4XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (-2) (0) (9850066508736996721 / 9765625000000000000) (0 / 1)

private theorem manuscriptCase2X4XV1_arg_eq : barrierCase2X4XV1LogArg = barrierComplex (3138481561 / 6250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV1LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV1Interval.1 : ℝ) (manuscriptCase2X4XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X4XV1LogArg).re ∈ _
  rw [manuscriptCase2X4XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X4XV1LogArg (-2) (0) (9850066508736996721 / 9765625000000000000) (3138481561 / 6250000000) (0 / 1)
  have hratio : ((0 / 1) / (3138481561 / 6250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV1_rounded_endpoints :
    (-306649335840158550070270678213600851397 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X4XV1Interval.1 ∧ manuscriptCase2X4XV1Interval.2 ≤ (-153324667920079275005075506617339021779 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-306649335840158550070270678213600851397 / 10000000000000000000000000000000000000000) : ℝ) ((-153324667920079275005075506617339021779 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-306649335840158550070270678213600851397 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV1Interval.2 : ℝ) ≤ ((-153324667920079275005075506617339021779 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV1_exact_interval.1, manuscriptCase2X4XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X4XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (1) (0) (1325608067877186289249 / 1250000000000000000000) (0 / 1)

private theorem manuscriptCase2X4XV2_arg_eq : barrierCase2X4XV2LogArg = barrierComplex (36408900943 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X4XV2LogArg, Case2PointData.X4, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X4XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X4XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X4XV2Interval.1 : ℝ) (manuscriptCase2X4XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X4XV2LogArg).re ∈ _
  rw [manuscriptCase2X4XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X4XV2LogArg (1) (0) (1325608067877186289249 / 1250000000000000000000) (36408900943 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (36408900943 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X4XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X4XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X4XV2_rounded_endpoints :
    (19138208732399763834145338764068018231 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X4XV2Interval.1 ∧ manuscriptCase2X4XV2Interval.2 ≤ (47845521830999409593957242571948733921 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X4XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X4XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X4 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((19138208732399763834145338764068018231 / 2000000000000000000000000000000000000000) : ℝ) ((47845521830999409593957242571948733921 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((19138208732399763834145338764068018231 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X4XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X4XV2Interval.2 : ℝ) ≤ ((47845521830999409593957242571948733921 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X4XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X4XV2_exact_interval.1, manuscriptCase2X4XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
