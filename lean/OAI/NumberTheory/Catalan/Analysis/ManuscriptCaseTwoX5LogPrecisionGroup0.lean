import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX5Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X5XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (2) (0) (14461960189749012657649 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X5XP0_arg_eq : barrierCase2X5XP0LogArg = barrierComplex (120257890343 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XP0LogArg, Case2PointData.X5, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XP0Interval.1 : ℝ) (manuscriptCase2X5XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X5XP0LogArg).re ∈ _
  rw [manuscriptCase2X5XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X5XP0LogArg (2) (0) (14461960189749012657649 / 10000000000000000000000) (120257890343 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (120257890343 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XP0_rounded_endpoints :
    (-1280557872690313289064736457283851469 / 7812500000000000000000000000000000000) ≤ manuscriptCase2X5XP0Interval.1 ∧ manuscriptCase2X5XP0Interval.2 ≤ (-819557038521800504875315602016646303997 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-1280557872690313289064736457283851469 / 7812500000000000000000000000000000000) : ℝ) ((-819557038521800504875315602016646303997 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1280557872690313289064736457283851469 / 7812500000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XP0Interval.2 : ℝ) ≤ ((-819557038521800504875315602016646303997 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XP0_exact_interval.1, manuscriptCase2X5XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (2) (0) (108779519132349219760369 / 62500000000000000000000) (0 / 1)

private theorem manuscriptCase2X5XP1_arg_eq : barrierCase2X5XP1LogArg = barrierComplex (329817402713 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XP1LogArg, Case2PointData.X5, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XP1Interval.1 : ℝ) (manuscriptCase2X5XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X5XP1LogArg).re ∈ _
  rw [manuscriptCase2X5XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X5XP1LogArg (2) (0) (108779519132349219760369 / 62500000000000000000000) (329817402713 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (329817402713 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XP1_rounded_endpoints :
    (-415549301888917176214371501055517321209 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XP1Interval.1 ∧ manuscriptCase2X5XP1Interval.2 ≤ (-415549301888917176156517656729128780951 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-415549301888917176214371501055517321209 / 10000000000000000000000000000000000000000) : ℝ) ((-415549301888917176156517656729128780951 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-415549301888917176214371501055517321209 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XP1Interval.2 : ℝ) ≤ ((-415549301888917176156517656729128780951 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XP1_exact_interval.1, manuscriptCase2X5XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X5XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-1) (1) (360097641713480519809 / 312500000000000000000) (76748209 / 1576748209)

private theorem manuscriptCase2X5XP2_arg_eq : barrierCase2X5XP2LogArg = barrierComplex (51 / 100) (14054719553 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X5XP2LogArg, Case2PointData.X5, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X5XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X5XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X5XP2Interval.1 : ℝ) (manuscriptCase2X5XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X5XP2LogArg).re ∈ _
  rw [manuscriptCase2X5XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X5XP2LogArg (-1) (1) (360097641713480519809 / 312500000000000000000) (26804719553 / 25000000000) (1304719553 / 25000000000)
  have hratio : ((1304719553 / 25000000000) / (26804719553 / 25000000000) : ℚ) = (76748209 / 1576748209) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X5XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X5XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X5XP2_rounded_endpoints :
    (-833998003865521440247376923386073688913 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X5XP2Interval.1 ∧ manuscriptCase2X5XP2Interval.2 ≤ (-833998003865521324127940470416114870293 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X5XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X5XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X5 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-833998003865521440247376923386073688913 / 10000000000000000000000000000000000000000) : ℝ) ((-833998003865521324127940470416114870293 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-833998003865521440247376923386073688913 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X5XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X5XP2Interval.2 : ℝ) ≤ ((-833998003865521324127940470416114870293 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X5XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X5XP2_exact_interval.1, manuscriptCase2X5XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
