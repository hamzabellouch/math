import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX7

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X7XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (2586595088738555279089 / 2500000000000000000000) (9305648217 / 50000000000)

private theorem manuscriptCase2X7XV7_arg_eq : barrierCase2X7XV7LogArg = barrierComplex (1 / 1) (9305648217 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV7LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV7Interval.1 : ℝ) (manuscriptCase2X7XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X7XV7LogArg).re ∈ _
  rw [manuscriptCase2X7XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X7XV7LogArg (0) (0) (2586595088738555279089 / 2500000000000000000000) (1 / 1) (9305648217 / 50000000000)
  have hratio : ((9305648217 / 50000000000) / (1 / 1) : ℚ) = (9305648217 / 50000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV7_rounded_endpoints :
    (-60885763100300347761581121884050146503 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X7XV7Interval.1 ∧ manuscriptCase2X7XV7Interval.2 ≤ (-304428815501501738807905609420250732463 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-60885763100300347761581121884050146503 / 2000000000000000000000000000000000000000) : ℝ) ((-304428815501501738807905609420250732463 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-60885763100300347761581121884050146503 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV7Interval.2 : ℝ) ≤ ((-304428815501501738807905609420250732463 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV7_exact_interval.1, manuscriptCase2X7XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (1039000931262607841190689 / 1000000000000000000000000) (197486534383 / 1000000000000)

private theorem manuscriptCase2X7XV9_arg_eq : barrierCase2X7XV9LogArg = barrierComplex (1 / 1) (197486534383 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV9LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV9Interval.1 : ℝ) (manuscriptCase2X7XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X7XV9LogArg).re ∈ _
  rw [manuscriptCase2X7XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X7XV9LogArg (0) (0) (1039000931262607841190689 / 1000000000000000000000000) (1 / 1) (197486534383 / 1000000000000)
  have hratio : ((197486534383 / 1000000000000) / (1 / 1) : ℚ) = (197486534383 / 1000000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV9_rounded_endpoints :
    (54864414271754730844530383044778113061 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X7XV9Interval.1 ∧ manuscriptCase2X7XV9Interval.2 ≤ (109728828543509461689060766089556226491 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((54864414271754730844530383044778113061 / 5000000000000000000000000000000000000000) : ℝ) ((109728828543509461689060766089556226491 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((54864414271754730844530383044778113061 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV9Interval.2 : ℝ) ≤ ((109728828543509461689060766089556226491 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV9_exact_interval.1, manuscriptCase2X7XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X7XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (406799038241056824905401 / 390625000000000000000000) (127177192299 / 625000000000)

private theorem manuscriptCase2X7XV11_arg_eq : barrierCase2X7XV11LogArg = barrierComplex (1 / 1) (127177192299 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X7XV11LogArg, Case2PointData.X7, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X7XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X7XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X7XV11Interval.1 : ℝ) (manuscriptCase2X7XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X7XV11LogArg).re ∈ _
  rw [manuscriptCase2X7XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X7XV11LogArg (0) (0) (406799038241056824905401 / 390625000000000000000000) (1 / 1) (127177192299 / 625000000000)
  have hratio : ((127177192299 / 625000000000) / (1 / 1) : ℚ) = (127177192299 / 625000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X7XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X7XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X7XV11_rounded_endpoints :
    (-26985060677081297103461016704540354537 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X7XV11Interval.1 ∧ manuscriptCase2X7XV11Interval.2 ≤ (-215880485416650376827688133636322833387 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X7XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X7XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X7 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-26985060677081297103461016704540354537 / 1250000000000000000000000000000000000000) : ℝ) ((-215880485416650376827688133636322833387 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-26985060677081297103461016704540354537 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X7XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X7XV11Interval.2 : ℝ) ≤ ((-215880485416650376827688133636322833387 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X7XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X7XV11_exact_interval.1, manuscriptCase2X7XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
