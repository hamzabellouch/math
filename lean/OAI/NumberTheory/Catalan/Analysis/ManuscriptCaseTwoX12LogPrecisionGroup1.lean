import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX12Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X12XP4Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1231651 / 100000000) (-1200529 / 20000000) (-1) (-2) (6317188448321037607081 / 5000000000000000000000) (27750000000 / 74479030259)

private theorem manuscriptCase2X12XP4_arg_eq : barrierCase2X12XP4LogArg = barrierComplex (111 / 400) (-74479030259 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XP4LogArg, Case2PointData.X12, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XP4_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 = barrierComplex (-1231651 / 100000000) (-1200529 / 20000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XP4_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XP4Interval.1 : ℝ) (manuscriptCase2X12XP4Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 4 (0, 0)).2 * Complex.log barrierCase2X12XP4LogArg).re ∈ _
  rw [manuscriptCase2X12XP4_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1231651 / 100000000) (-1200529 / 20000000)
    barrierCase2X12XP4LogArg (-1) (-2) (6317188448321037607081 / 5000000000000000000000) (74479030259 / 50000000000) (111 / 200)
  have hratio : ((111 / 200) / (74479030259 / 50000000000) : ℚ) = (27750000000 / 74479030259) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XP4Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XP4_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XP4_rounded_endpoints :
    (-700520734149580162967061069096580618373 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XP4Interval.1 ∧ manuscriptCase2X12XP4Interval.2 ≤ (-700520734149580119436938391489020094809 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XP4Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XP4_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 4 (0, 0)) ∈ Set.Icc ((-700520734149580162967061069096580618373 / 10000000000000000000000000000000000000000) : ℝ) ((-700520734149580119436938391489020094809 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-700520734149580162967061069096580618373 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XP4Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP4_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XP4Interval.2 : ℝ) ≤ ((-700520734149580119436938391489020094809 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP4_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XP4_exact_interval.1, manuscriptCase2X12XP4_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XP6Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-1612959 / 50000000) (-4464117 / 50000000) (-2) (-2) (644073634843312672210141 / 390625000000000000000000) (101814253179 / 796057468210)

private theorem manuscriptCase2X12XP6_arg_eq : barrierCase2X12XP6LogArg = barrierComplex (101814253179 / 1250000000000) (-79605746821 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XP6LogArg, Case2PointData.X12, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XP6_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 = barrierComplex (-1612959 / 50000000) (-4464117 / 50000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XP6_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XP6Interval.1 : ℝ) (manuscriptCase2X12XP6Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 6 (0, 0)).2 * Complex.log barrierCase2X12XP6LogArg).re ∈ _
  rw [manuscriptCase2X12XP6_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-1612959 / 50000000) (-4464117 / 50000000)
    barrierCase2X12XP6LogArg (-2) (-2) (644073634843312672210141 / 390625000000000000000000) (79605746821 / 62500000000) (101814253179 / 625000000000)
  have hratio : ((101814253179 / 625000000000) / (79605746821 / 62500000000) : ℚ) = (101814253179 / 796057468210) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XP6Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XP6_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XP6_rounded_endpoints :
    (-1145924726295736610965710039445533827073 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X12XP6Interval.1 ∧ manuscriptCase2X12XP6Interval.2 ≤ (-1145924726295736546188553738797854988147 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XP6Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XP6_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 6 (0, 0)) ∈ Set.Icc ((-1145924726295736610965710039445533827073 / 10000000000000000000000000000000000000000) : ℝ) ((-1145924726295736546188553738797854988147 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1145924726295736610965710039445533827073 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XP6Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP6_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XP6Interval.2 : ℝ) ≤ ((-1145924726295736546188553738797854988147 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP6_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XP6_exact_interval.1, manuscriptCase2X12XP6_exact_interval.2.trans hhi⟩

def manuscriptCase2X12XP8Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-32899 / 1562500) (9091287 / 100000000) (0) (-2) (1578607415900249392210141 / 1562500000000000000000000) (303345746821 / 1219257468210)

private theorem manuscriptCase2X12XP8_arg_eq : barrierCase2X12XP8LogArg = barrierComplex (303345746821 / 1250000000000) (-121925746821 / 125000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X12XP8LogArg, Case2PointData.X12, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X12XP8_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 = barrierComplex (-32899 / 1562500) (9091287 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X12XP8_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc (manuscriptCase2X12XP8Interval.1 : ℝ) (manuscriptCase2X12XP8Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 8 (0, 0)).2 * Complex.log barrierCase2X12XP8LogArg).re ∈ _
  rw [manuscriptCase2X12XP8_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-32899 / 1562500) (9091287 / 100000000)
    barrierCase2X12XP8LogArg (0) (-2) (1578607415900249392210141 / 1562500000000000000000000) (121925746821 / 62500000000) (303345746821 / 625000000000)
  have hratio : ((303345746821 / 625000000000) / (121925746821 / 62500000000) : ℚ) = (303345746821 / 1219257468210) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X12XP8Interval
  apply h
  all_goals
    try rw [manuscriptCase2X12XP8_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X12XP8_rounded_endpoints :
    (602645056518372162347212661026374732953 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X12XP8Interval.1 ∧ manuscriptCase2X12XP8Interval.2 ≤ (1205290113036744390610220748142025946887 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X12XP8Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X12XP8_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X12 : ℝ) (barrierP2Tail.getD 8 (0, 0)) ∈ Set.Icc ((602645056518372162347212661026374732953 / 5000000000000000000000000000000000000000) : ℝ) ((1205290113036744390610220748142025946887 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((602645056518372162347212661026374732953 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X12XP8Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP8_rounded_endpoints.1
  have hhi : (manuscriptCase2X12XP8Interval.2 : ℝ) ≤ ((1205290113036744390610220748142025946887 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X12XP8_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X12XP8_exact_interval.1, manuscriptCase2X12XP8_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
