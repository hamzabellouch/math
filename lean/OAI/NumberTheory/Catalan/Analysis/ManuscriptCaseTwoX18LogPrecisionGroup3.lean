import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX18

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X18XV3Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2466317 / 50000000) (0 / 1) (1) (0) (1521 / 800) (0 / 1)

private theorem manuscriptCase2X18XV3_arg_eq : barrierCase2X18XV3LogArg = barrierComplex (39 / 20) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV3LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV3_weight_eq : (barrierV2Tail.getD 3 (0, 0)).2 = barrierComplex (-2466317 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV3_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV3Interval.1 : ℝ) (manuscriptCase2X18XV3Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 3 (0, 0)).2 * Complex.log barrierCase2X18XV3LogArg).re ∈ _
  rw [manuscriptCase2X18XV3_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2466317 / 50000000) (0 / 1)
    barrierCase2X18XV3LogArg (1) (0) (1521 / 800) (39 / 20) (0 / 1)
  have hratio : ((0 / 1) / (39 / 20) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV3Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV3_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV3_rounded_endpoints :
    (-32941578693653455661020317781561685293 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X18XV3Interval.1 ∧ manuscriptCase2X18XV3Interval.2 ≤ (-65883157387306911314896499446545789779 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV3Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV3_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 3 (0, 0)) ∈ Set.Icc ((-32941578693653455661020317781561685293 / 1000000000000000000000000000000000000000) : ℝ) ((-65883157387306911314896499446545789779 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-32941578693653455661020317781561685293 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV3Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV3_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV3Interval.2 : ℝ) ≤ ((-65883157387306911314896499446545789779 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV3_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV3_exact_interval.1, manuscriptCase2X18XV3_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XV4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (11618157 / 100000000) (0 / 1) (1) (0) (30752 / 15625) (0 / 1)

private theorem manuscriptCase2X18XV4_arg_eq : barrierCase2X18XV4LogArg = barrierComplex (248 / 125) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV4LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV4_weight_eq : (barrierV2Tail.getD 4 (0, 0)).2 = barrierComplex (11618157 / 100000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV4_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV4Interval.1 : ℝ) (manuscriptCase2X18XV4Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X18XV4LogArg).re ∈ _
  rw [manuscriptCase2X18XV4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (11618157 / 100000000) (0 / 1)
    barrierCase2X18XV4LogArg (1) (0) (30752 / 15625) (248 / 125) (0 / 1)
  have hratio : ((0 / 1) / (248 / 125) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV4_rounded_endpoints :
    (795977373602301988309634880817476682167 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X18XV4Interval.1 ∧ manuscriptCase2X18XV4Interval.2 ≤ (79597737360230198842303612384917478081 / 1000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV4_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 4 (0, 0)) ∈ Set.Icc ((795977373602301988309634880817476682167 / 10000000000000000000000000000000000000000) : ℝ) ((79597737360230198842303612384917478081 / 1000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((795977373602301988309634880817476682167 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV4_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV4Interval.2 : ℝ) ≤ ((79597737360230198842303612384917478081 / 1000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV4_exact_interval.1, manuscriptCase2X18XV4_exact_interval.2.trans hhi⟩

def manuscriptCase2X18XV5Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (13619357 / 100000000) (600749 / 3125000) (0) (1) (4021 / 2500) (-11 / 89)

private theorem manuscriptCase2X18XV5_arg_eq : barrierCase2X18XV5LogArg = barrierComplex (1 / 1) (39 / 50) := by
  apply Complex.ext <;> norm_num [barrierCase2X18XV5LogArg, Case2PointData.X18, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X18XV5_weight_eq : (barrierV2Tail.getD 5 (0, 0)).2 = barrierComplex (13619357 / 100000000) (600749 / 3125000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X18XV5_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc (manuscriptCase2X18XV5Interval.1 : ℝ) (manuscriptCase2X18XV5Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 5 (0, 0)).2 * Complex.log barrierCase2X18XV5LogArg).re ∈ _
  rw [manuscriptCase2X18XV5_weight_eq]
  have h := manuscript_weighted_complex_log_interval (13619357 / 100000000) (600749 / 3125000)
    barrierCase2X18XV5LogArg (0) (1) (4021 / 2500) (89 / 50) (-11 / 50)
  have hratio : ((-11 / 50) / (89 / 50) : ℚ) = (-11 / 89) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X18XV5Interval
  apply h
  all_goals
    try rw [manuscriptCase2X18XV5_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X18XV5_rounded_endpoints :
    (-949823097259458581830779334828804597677 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X18XV5Interval.1 ∧ manuscriptCase2X18XV5Interval.2 ≤ (-949823097259458512139703426462791642787 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X18XV5Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X18XV5_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X18 : ℝ) (barrierV2Tail.getD 5 (0, 0)) ∈ Set.Icc ((-949823097259458581830779334828804597677 / 10000000000000000000000000000000000000000) : ℝ) ((-949823097259458512139703426462791642787 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-949823097259458581830779334828804597677 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X18XV5Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV5_rounded_endpoints.1
  have hhi : (manuscriptCase2X18XV5Interval.2 : ℝ) ≤ ((-949823097259458512139703426462791642787 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X18XV5_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X18XV5_exact_interval.1, manuscriptCase2X18XV5_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
