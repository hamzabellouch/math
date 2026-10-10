import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX14

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X14XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (-3) (0) (2369399531804781411961 / 1250000000000000000000) (0 / 1)

private theorem manuscriptCase2X14XP0_arg_eq : barrierCase2X14XP0LogArg = barrierComplex (48676478219 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XP0LogArg, Case2PointData.X14, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XP0Interval.1 : ℝ) (manuscriptCase2X14XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X14XP0LogArg).re ∈ _
  rw [manuscriptCase2X14XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X14XP0LogArg (-3) (0) (2369399531804781411961 / 1250000000000000000000) (48676478219 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (48676478219 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XP0_rounded_endpoints :
    (672344512453908222052351112209280437499 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X14XP0Interval.1 ∧ manuscriptCase2X14XP0Interval.2 ≤ (26893780498156328889816118373322108933 / 200000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((672344512453908222052351112209280437499 / 5000000000000000000000000000000000000000) : ℝ) ((26893780498156328889816118373322108933 / 200000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((672344512453908222052351112209280437499 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XP0Interval.2 : ℝ) ≤ ((26893780498156328889816118373322108933 / 200000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XP0_exact_interval.1, manuscriptCase2X14XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (-2) (0) (16706999126281517090041 / 15625000000000000000000) (0 / 1)

private theorem manuscriptCase2X14XP1_arg_eq : barrierCase2X14XP1LogArg = barrierComplex (129255557429 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XP1LogArg, Case2PointData.X14, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XP1Interval.1 : ℝ) (manuscriptCase2X14XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X14XP1LogArg).re ∈ _
  rw [manuscriptCase2X14XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X14XP1LogArg (-2) (0) (16706999126281517090041 / 15625000000000000000000) (129255557429 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (129255557429 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XP1_rounded_endpoints :
    (282537594800637869981867696162374881403 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X14XP1Interval.1 ∧ manuscriptCase2X14XP1Interval.2 ≤ (17658599675039866877481864066896336917 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((282537594800637869981867696162374881403 / 10000000000000000000000000000000000000000) : ℝ) ((17658599675039866877481864066896336917 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((282537594800637869981867696162374881403 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XP1Interval.2 : ℝ) ≤ ((17658599675039866877481864066896336917 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XP1_exact_interval.1, manuscriptCase2X14XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (0) (-1) (3239351553573026952201 / 2500000000000000000000) (-8461071617 / 25461071617)

private theorem manuscriptCase2X14XP2_arg_eq : barrierCase2X14XP2LogArg = barrierComplex (51 / 100) (-50883214851 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XP2LogArg, Case2PointData.X14, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XP2Interval.1 : ℝ) (manuscriptCase2X14XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X14XP2LogArg).re ∈ _
  rw [manuscriptCase2X14XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X14XP2LogArg (0) (-1) (3239351553573026952201 / 2500000000000000000000) (76383214851 / 50000000000) (-25383214851 / 50000000000)
  have hratio : ((-25383214851 / 50000000000) / (76383214851 / 50000000000) : ℚ) = (-8461071617 / 25461071617) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XP2_rounded_endpoints :
    (106845685913113283918831398050813041689 / 400000000000000000000000000000000000000) ≤ manuscriptCase2X14XP2Interval.1 ∧ manuscriptCase2X14XP2Interval.2 ≤ (1335571073913916106821340097961705534173 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X14 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((106845685913113283918831398050813041689 / 400000000000000000000000000000000000000) : ℝ) ((1335571073913916106821340097961705534173 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((106845685913113283918831398050813041689 / 400000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XP2Interval.2 : ℝ) ≤ ((1335571073913916106821340097961705534173 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XP2_exact_interval.1, manuscriptCase2X14XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
