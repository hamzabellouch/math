import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX12

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X12XV0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (15199211 / 100000000) (0 / 1) (0) (0) (284972193108636808329 / 156250000000000000000) (0 / 1)

private theorem manuscriptCase2X12XV0_arg_eq : barrierCase2X12XV0LogArg = barrierComplex (16881119427 / 12500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV0LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV0_weight_eq : (barrierV2Tail.getD 0 (0, 0)).2 = barrierComplex (15199211 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV0_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV0Interval.1 : ℝ) (manuscriptCase2X12XV0Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X12XV0LogArg).re ∈ _
  rw [manuscriptCase2X12XV0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (15199211 / 100000000) (0 / 1)
    barrierCase2X12XV0LogArg (0) (0) (284972193108636808329 / 156250000000000000000) (16881119427 / 12500000000) (0 / 1)
  have hratio : ((0 / 1) / (16881119427 / 12500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV0_rounded_endpoints :
    (456686375468791740505412105008259220149 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XV0Interval.1 ∧ manuscriptCase2X12XV0Interval.2 ≤ (456686375468791740506131730486558852177 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV0_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 0 (0, 0)) ∈ Set.Icc ((456686375468791740505412105008259220149 / 10000000000000000000000000000000000000000) : ℝ) ((456686375468791740506131730486558852177 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((456686375468791740505412105008259220149 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV0_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV0Interval.2 : ℝ) ≤ ((456686375468791740506131730486558852177 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV0_exact_interval.1, manuscriptCase2X12XV0_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XV1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2225831 / 50000000) (0 / 1) (1) (0) (1970770259465231274961 / 1953125000000000000000) (0 / 1)

private theorem manuscriptCase2X12XV1_arg_eq : barrierCase2X12XV1LogArg = barrierComplex (44393358281 / 31250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV1LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV1_weight_eq : (barrierV2Tail.getD 1 (0, 0)).2 = barrierComplex (2225831 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV1_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV1Interval.1 : ℝ) (manuscriptCase2X12XV1Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X12XV1LogArg).re ∈ _
  rw [manuscriptCase2X12XV1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2225831 / 50000000) (0 / 1)
    barrierCase2X12XV1LogArg (1) (0) (1970770259465231274961 / 1953125000000000000000) (44393358281 / 31250000000) (0 / 1)
  have hratio : ((0 / 1) / (44393358281 / 31250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV1_rounded_endpoints :
    (39071179414329967657739368757771628667 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X12XV1Interval.1 ∧ manuscriptCase2X12XV1Interval.2 ≤ (39071179414329967665254326880136979647 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV1_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 1 (0, 0)) ∈ Set.Icc ((39071179414329967657739368757771628667 / 2500000000000000000000000000000000000000) : ℝ) ((39071179414329967665254326880136979647 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((39071179414329967657739368757771628667 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV1_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV1Interval.2 : ℝ) ≤ ((39071179414329967665254326880136979647 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV1_exact_interval.1, manuscriptCase2X12XV1_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XV2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (1272699 / 50000000) (0 / 1) (-2) (0) (5899420675220053807809 / 3906250000000000000000) (0 / 1)

private theorem manuscriptCase2X12XV2_arg_eq : barrierCase2X12XV2LogArg = barrierComplex (76807686303 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XV2LogArg, Case2PointData.X12, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XV2_weight_eq : (barrierV2Tail.getD 2 (0, 0)).2 = barrierComplex (1272699 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XV2_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XV2Interval.1 : ℝ) (manuscriptCase2X12XV2Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X12XV2LogArg).re ∈ _
  rw [manuscriptCase2X12XV2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (1272699 / 50000000) (0 / 1)
    barrierCase2X12XV2LogArg (-2) (0) (5899420675220053807809 / 3906250000000000000000) (76807686303 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (76807686303 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XV2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XV2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XV2_rounded_endpoints :
    (-123963178570947107754900995667985619479 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XV2Interval.1 ∧ manuscriptCase2X12XV2Interval.2 ≤ (-123963178570947107720525412841246579211 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XV2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XV2_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X12 : ℝ) (barrierV2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-123963178570947107754900995667985619479 / 10000000000000000000000000000000000000000) : ℝ) ((-123963178570947107720525412841246579211 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-123963178570947107754900995667985619479 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XV2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV2_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XV2Interval.2 : ℝ) ≤ ((-123963178570947107720525412841246579211 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XV2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XV2_exact_interval.1, manuscriptCase2X12XV2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
