import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY7

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y7YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (649634763518684806729 / 625000000000000000000) (4750000000 / 25041410973)

private theorem manuscriptCase2Y7YV7_arg_eq : barrierCase2Y7YV7LogArg = barrierComplex (19 / 100) (-25041410973 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV7LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV7Interval.1 : ℝ) (manuscriptCase2Y7YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y7YV7LogArg).re ∈ _
  rw [manuscriptCase2Y7YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y7YV7LogArg (0) (-2) (649634763518684806729 / 625000000000000000000) (25041410973 / 12500000000) (19 / 50)
  have hratio : ((19 / 50) / (25041410973 / 12500000000) : ℚ) = (4750000000 / 25041410973) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV7_rounded_endpoints :
    (-2057774116618837466849197873174796993227 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV7Interval.1 ∧ manuscriptCase2Y7YV7Interval.2 ≤ (-411554823323767471481653203024574756321 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-2057774116618837466849197873174796993227 / 10000000000000000000000000000000000000000) : ℝ) ((-411554823323767471481653203024574756321 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-2057774116618837466849197873174796993227 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV7Interval.2 : ℝ) ≤ ((-411554823323767471481653203024574756321 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV7_exact_interval.1, manuscriptCase2Y7YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y7YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (284357409359029511534329 / 250000000000000000000000) (43987500000 / 531434388427)

private theorem manuscriptCase2Y7YV9_arg_eq : barrierCase2Y7YV9LogArg = barrierComplex (3519 / 40000) (-531434388427 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV9LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV9Interval.1 : ℝ) (manuscriptCase2Y7YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y7YV9LogArg).re ∈ _
  rw [manuscriptCase2Y7YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y7YV9LogArg (0) (-2) (284357409359029511534329 / 250000000000000000000000) (531434388427 / 250000000000) (3519 / 20000)
  have hratio : ((3519 / 20000) / (531434388427 / 250000000000) : ℚ) = (43987500000 / 531434388427) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV9_rounded_endpoints :
    (907947100183126773133523475816290187221 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV9Interval.1 ∧ manuscriptCase2Y7YV9Interval.2 ≤ (226986775045781704079510417603415836759 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((907947100183126773133523475816290187221 / 10000000000000000000000000000000000000000) : ℝ) ((226986775045781704079510417603415836759 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((907947100183126773133523475816290187221 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV9Interval.2 : ℝ) ≤ ((226986775045781704079510417603415836759 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV9_exact_interval.1, manuscriptCase2Y7YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y7YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (117221570286101017790161 / 97656250000000000000000) (9920000000 / 342232616631)

private theorem manuscriptCase2Y7YV11_arg_eq : barrierCase2Y7YV11LogArg = barrierComplex (496 / 15625) (-342232616631 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y7YV11LogArg, Case2PointData.Y7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y7YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y7YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y7YV11Interval.1 : ℝ) (manuscriptCase2Y7YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y7YV11LogArg).re ∈ _
  rw [manuscriptCase2Y7YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y7YV11LogArg (0) (-2) (117221570286101017790161 / 97656250000000000000000) (342232616631 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (342232616631 / 156250000000) : ℚ) = (9920000000 / 342232616631) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y7YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y7YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y7YV11_rounded_endpoints :
    (-841738677436948716023070161645948544329 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y7YV11Interval.1 ∧ manuscriptCase2Y7YV11Interval.2 ≤ (-13152166834952323072823848423665521581 / 78125000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y7YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y7YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y7 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-841738677436948716023070161645948544329 / 5000000000000000000000000000000000000000) : ℝ) ((-13152166834952323072823848423665521581 / 78125000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-841738677436948716023070161645948544329 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y7YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y7YV11Interval.2 : ℝ) ≤ ((-13152166834952323072823848423665521581 / 78125000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y7YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y7YV11_exact_interval.1, manuscriptCase2Y7YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
