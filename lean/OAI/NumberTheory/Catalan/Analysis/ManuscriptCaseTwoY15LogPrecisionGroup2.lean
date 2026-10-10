import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY15

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y15YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-3) (-2) (1193 / 625) (19 / 45)

private theorem manuscriptCase2Y15YV7_arg_eq : barrierCase2Y15YV7LogArg = barrierComplex (19 / 100) (-9 / 20) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV7LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV7Interval.1 : ℝ) (manuscriptCase2Y15YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y15YV7LogArg).re ∈ _
  rw [manuscriptCase2Y15YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y15YV7LogArg (-3) (-2) (1193 / 625) (9 / 10) (19 / 50)
  have hratio : ((19 / 50) / (9 / 10) : ℚ) = (19 / 45) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV7_rounded_endpoints :
    (-115629824700745727870663481785226944189 / 400000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV7Interval.1 ∧ manuscriptCase2Y15YV7Interval.2 ≤ (-578149123503728617396981650831013658339 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-115629824700745727870663481785226944189 / 400000000000000000000000000000000000000) : ℝ) ((-578149123503728617396981650831013658339 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-115629824700745727870663481785226944189 / 400000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV7Interval.2 : ℝ) ≤ ((-578149123503728617396981650831013658339 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV7_exact_interval.1, manuscriptCase2Y15YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y15YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-3) (-2) (377193361 / 200000000) (3519 / 19100)

private theorem manuscriptCase2Y15YV9_arg_eq : barrierCase2Y15YV9LogArg = barrierComplex (3519 / 40000) (-191 / 400) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV9LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV9Interval.1 : ℝ) (manuscriptCase2Y15YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y15YV9LogArg).re ∈ _
  rw [manuscriptCase2Y15YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y15YV9LogArg (-3) (-2) (377193361 / 200000000) (191 / 200) (3519 / 20000)
  have hratio : ((3519 / 20000) / (191 / 200) : ℚ) = (3519 / 19100) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV9_rounded_endpoints :
    (146315663937703956631289506359193298149 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV9Interval.1 ∧ manuscriptCase2Y15YV9Interval.2 ≤ (585262655750815869778527978792157680083 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((146315663937703956631289506359193298149 / 2500000000000000000000000000000000000000) : ℝ) ((585262655750815869778527978792157680083 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((146315663937703956631289506359193298149 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV9Interval.2 : ℝ) ≤ ((585262655750815869778527978792157680083 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV9_exact_interval.1, manuscriptCase2Y15YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y15YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-3) (-2) (474749378 / 244140625) (992 / 15375)

private theorem manuscriptCase2Y15YV11_arg_eq : barrierCase2Y15YV11LogArg = barrierComplex (496 / 15625) (-123 / 250) := by
  apply Complex.ext <;> norm_num [barrierCase2Y15YV11LogArg, Case2PointData.Y15, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y15YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y15YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y15YV11Interval.1 : ℝ) (manuscriptCase2Y15YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y15YV11LogArg).re ∈ _
  rw [manuscriptCase2Y15YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y15YV11LogArg (-3) (-2) (474749378 / 244140625) (123 / 125) (992 / 15625)
  have hratio : ((992 / 15625) / (123 / 125) : ℚ) = (992 / 15375) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y15YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y15YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y15YV11_rounded_endpoints :
    (-312585560837954611202973582423025780081 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2Y15YV11Interval.1 ∧ manuscriptCase2Y15YV11Interval.2 ≤ (-1562927804189772977267701274282361102103 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y15YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y15YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y15 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-312585560837954611202973582423025780081 / 2000000000000000000000000000000000000000) : ℝ) ((-1562927804189772977267701274282361102103 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-312585560837954611202973582423025780081 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y15YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y15YV11Interval.2 : ℝ) ≤ ((-1562927804189772977267701274282361102103 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y15YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y15YV11_exact_interval.1, manuscriptCase2Y15YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
