import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY14

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y14YV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2466317 / 50000000) (0 / 1) (-16) (0) (10064768335175761 / 9536743164062500) (0 / 1)

private theorem manuscriptCase2Y14YV3_arg_eq : barrierCase2Y14YV3LogArg = barrierComplex (100323319 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV3LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV3_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) = barrierComplex (2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV3_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV3Interval.1 : ℝ) (manuscriptCase2Y14YV3Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 3 (0, 0)).2) * Complex.log barrierCase2Y14YV3LogArg).re ∈ _
  rw [manuscriptCase2Y14YV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2466317 / 50000000) (0 / 1)
    barrierCase2Y14YV3LogArg (-16) (0) (10064768335175761 / 9536743164062500) (100323319 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (100323319 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV3_rounded_endpoints :
    (-2721942343644718140988944446224474501321 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV3Interval.1 ∧ manuscriptCase2Y14YV3Interval.2 ≤ (-1360971171822359070228011468864817814667 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV3_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-2721942343644718140988944446224474501321 / 10000000000000000000000000000000000000000) : ℝ) ((-1360971171822359070228011468864817814667 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2721942343644718140988944446224474501321 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV3_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV3Interval.2 : ℝ) ≤ ((-1360971171822359070228011468864817814667 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV3_exact_interval.1, manuscriptCase2Y14YV3_exact_interval.2.trans hhi⟩

def manuscriptCase2Y14YV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-11618157 / 100000000) (0 / 1) (-19) (0) (2596578169018423328 / 1490116119384765625) (0 / 1)

private theorem manuscriptCase2Y14YV4_arg_eq : barrierCase2Y14YV4LogArg = barrierComplex (284856223 / 156250000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV4LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV4_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) = barrierComplex (-11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV4_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV4Interval.1 : ℝ) (manuscriptCase2Y14YV4Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 4 (0, 0)).2) * Complex.log barrierCase2Y14YV4LogArg).re ∈ _
  rw [manuscriptCase2Y14YV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-11618157 / 100000000) (0 / 1)
    barrierCase2Y14YV4LogArg (-19) (0) (2596578169018423328 / 1490116119384765625) (284856223 / 156250000000) (0 / 1)
  have hratio : ((0 / 1) / (284856223 / 156250000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV4_rounded_endpoints :
    (366391825422402914991881072005237176539 / 500000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV4Interval.1 ∧ manuscriptCase2Y14YV4Interval.2 ≤ (1465567301689611660265647090622382928677 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV4_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((366391825422402914991881072005237176539 / 500000000000000000000000000000000000000) : ℝ) ((1465567301689611660265647090622382928677 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((366391825422402914991881072005237176539 / 500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV4_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV4Interval.2 : ℝ) ≤ ((1465567301689611660265647090622382928677 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV4_exact_interval.1, manuscriptCase2Y14YV4_exact_interval.2.trans hhi⟩

def manuscriptCase2Y14YV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-13619357 / 100000000) (-600749 / 3125000) (1) (-2) (10090142371451407000921 / 7812500000000000000000) (24475000000 / 97422362661)

private theorem manuscriptCase2Y14YV5_arg_eq : barrierCase2Y14YV5LogArg = barrierComplex (979 / 2500) (-97422362661 / 62500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y14YV5LogArg, Case2PointData.Y14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y14YV5_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) = barrierComplex (-13619357 / 100000000) (-600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y14YV5_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2Y14YV5Interval.1 : ℝ) (manuscriptCase2Y14YV5Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 5 (0, 0)).2) * Complex.log barrierCase2Y14YV5LogArg).re ∈ _
  rw [manuscriptCase2Y14YV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-13619357 / 100000000) (-600749 / 3125000)
    barrierCase2Y14YV5LogArg (1) (-2) (10090142371451407000921 / 7812500000000000000000) (97422362661 / 31250000000) (979 / 1250)
  have hratio : ((979 / 1250) / (97422362661 / 31250000000) : ℚ) = (24475000000 / 97422362661) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y14YV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y14YV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y14YV5_rounded_endpoints :
    (-1596378123427554182079670596139729542217 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y14YV5Interval.1 ∧ manuscriptCase2Y14YV5Interval.2 ≤ (-1596378123427554112342612515173243298791 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y14YV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y14YV5_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y14 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-1596378123427554182079670596139729542217 / 5000000000000000000000000000000000000000) : ℝ) ((-1596378123427554112342612515173243298791 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1596378123427554182079670596139729542217 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y14YV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV5_rounded_endpoints.1
  have hhi : (manuscriptCase2Y14YV5Interval.2 : ℝ) ≤ ((-1596378123427554112342612515173243298791 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y14YV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y14YV5_exact_interval.1, manuscriptCase2Y14YV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
