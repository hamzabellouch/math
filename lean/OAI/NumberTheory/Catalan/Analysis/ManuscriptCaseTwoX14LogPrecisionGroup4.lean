import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX14

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X14XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (14279943384477860880169 / 10000000000000000000000) (34578723763 / 165421276237)

private theorem manuscriptCase2X14XV7_arg_eq : barrierCase2X14XV7LogArg = barrierComplex (1 / 1) (-65421276237 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV7LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV7Interval.1 : ℝ) (manuscriptCase2X14XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X14XV7LogArg).re ∈ _
  rw [manuscriptCase2X14XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X14XV7LogArg (0) (-1) (14279943384477860880169 / 10000000000000000000000) (165421276237 / 100000000000) (34578723763 / 100000000000)
  have hratio : ((34578723763 / 100000000000) / (165421276237 / 100000000000) : ℚ) = (34578723763 / 165421276237) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV7_rounded_endpoints :
    (119063427651905564227554812326728109407 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X14XV7Interval.1 ∧ manuscriptCase2X14XV7Interval.2 ≤ (74414642282440984482279998833152605941 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((119063427651905564227554812326728109407 / 2000000000000000000000000000000000000000) : ℝ) ((74414642282440984482279998833152605941 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((119063427651905564227554812326728109407 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV7Interval.2 : ℝ) ≤ ((74414642282440984482279998833152605941 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV7_exact_interval.1, manuscriptCase2X14XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (5927612526038726453943769 / 4000000000000000000000000) (611615137637 / 3388384862363)

private theorem manuscriptCase2X14XV9_arg_eq : barrierCase2X14XV9LogArg = barrierComplex (1 / 1) (-1388384862363 / 2000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV9LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV9Interval.1 : ℝ) (manuscriptCase2X14XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X14XV9LogArg).re ∈ _
  rw [manuscriptCase2X14XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X14XV9LogArg (0) (-1) (5927612526038726453943769 / 4000000000000000000000000) (3388384862363 / 2000000000000) (611615137637 / 2000000000000)
  have hratio : ((611615137637 / 2000000000000) / (3388384862363 / 2000000000000) : ℚ) = (611615137637 / 3388384862363) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV9_rounded_endpoints :
    (-53405885005552887152389840950728257321 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X14XV9Interval.1 ∧ manuscriptCase2X14XV9Interval.2 ≤ (-106811770011105768906714907565982321239 / 2500000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-53405885005552887152389840950728257321 / 1250000000000000000000000000000000000000) : ℝ) ((-106811770011105768906714907565982321239 / 2500000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-53405885005552887152389840950728257321 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV9Interval.2 : ℝ) ≤ ((-106811770011105768906714907565982321239 / 2500000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV9_exact_interval.1, manuscriptCase2X14XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X14XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2361898314367476015507121 / 1562500000000000000000000) (355909224761 / 2144090775239)

private theorem manuscriptCase2X14XV11_arg_eq : barrierCase2X14XV11LogArg = barrierComplex (1 / 1) (-894090775239 / 1250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X14XV11LogArg, Case2PointData.X14, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X14XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X14XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X14XV11Interval.1 : ℝ) (manuscriptCase2X14XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X14XV11LogArg).re ∈ _
  rw [manuscriptCase2X14XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X14XV11LogArg (0) (-1) (2361898314367476015507121 / 1562500000000000000000000) (2144090775239 / 1250000000000) (355909224761 / 1250000000000)
  have hratio : ((355909224761 / 1250000000000) / (2144090775239 / 1250000000000) : ℚ) = (355909224761 / 2144090775239) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X14XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X14XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X14XV11_rounded_endpoints :
    (5432817836947385480575752528097532769 / 78125000000000000000000000000000000000) ≤ manuscriptCase2X14XV11Interval.1 ∧ manuscriptCase2X14XV11Interval.2 ≤ (347700341564632690438020093103151234823 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X14XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X14XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X14 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((5432817836947385480575752528097532769 / 78125000000000000000000000000000000000) : ℝ) ((347700341564632690438020093103151234823 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((5432817836947385480575752528097532769 / 78125000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X14XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X14XV11Interval.2 : ℝ) ≤ ((347700341564632690438020093103151234823 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X14XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X14XV11_exact_interval.1, manuscriptCase2X14XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
