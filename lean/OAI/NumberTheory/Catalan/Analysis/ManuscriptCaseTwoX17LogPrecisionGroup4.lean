import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX17

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X17XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (17636675821913267592841 / 10000000000000000000000) (12611924029 / 187388075971)

private theorem manuscriptCase2X17XV7_arg_eq : barrierCase2X17XV7LogArg = barrierComplex (1 / 1) (-87388075971 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV7LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV7Interval.1 : ℝ) (manuscriptCase2X17XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X17XV7LogArg).re ∈ _
  rw [manuscriptCase2X17XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X17XV7LogArg (0) (-1) (17636675821913267592841 / 10000000000000000000000) (187388075971 / 100000000000) (12611924029 / 100000000000)
  have hratio : ((12611924029 / 100000000000) / (187388075971 / 100000000000) : ℚ) = (12611924029 / 187388075971) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV7_rounded_endpoints :
    (639503131669146851071829689902224797029 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV7Interval.1 ∧ manuscriptCase2X17XV7Interval.2 ≤ (319751565834573452896197107948030778703 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((639503131669146851071829689902224797029 / 10000000000000000000000000000000000000000) : ℝ) ((319751565834573452896197107948030778703 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((639503131669146851071829689902224797029 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV7Interval.2 : ℝ) ≤ ((319751565834573452896197107948030778703 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV7_exact_interval.1, manuscriptCase2X17XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (7439426798261949568573241 / 4000000000000000000000000) (145430832171 / 3854569167829)

private theorem manuscriptCase2X17XV9_arg_eq : barrierCase2X17XV9LogArg = barrierComplex (1 / 1) (-1854569167829 / 2000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV9LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV9Interval.1 : ℝ) (manuscriptCase2X17XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X17XV9LogArg).re ∈ _
  rw [manuscriptCase2X17XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X17XV9LogArg (0) (-1) (7439426798261949568573241 / 4000000000000000000000000) (3854569167829 / 2000000000000) (145430832171 / 2000000000000)
  have hratio : ((145430832171 / 2000000000000) / (3854569167829 / 2000000000000) : ℚ) = (145430832171 / 3854569167829) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV9_rounded_endpoints :
    (-274582551529306563789847020449376541191 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV9Interval.1 ∧ manuscriptCase2X17XV9Interval.2 ≤ (-68645637882326638248368622994088757089 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-274582551529306563789847020449376541191 / 5000000000000000000000000000000000000000) : ℝ) ((-68645637882326638248368622994088757089 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-274582551529306563789847020449376541191 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV9Interval.2 : ℝ) ≤ ((-68645637882326638248368622994088757089 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV9_exact_interval.1, manuscriptCase2X17XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X17XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (2988861339626244758173969 / 1562500000000000000000000) (55696295063 / 2444303704937)

private theorem manuscriptCase2X17XV11_arg_eq : barrierCase2X17XV11LogArg = barrierComplex (1 / 1) (-1194303704937 / 1250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X17XV11LogArg, Case2PointData.X17, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X17XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X17XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X17XV11Interval.1 : ℝ) (manuscriptCase2X17XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X17XV11LogArg).re ∈ _
  rw [manuscriptCase2X17XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X17XV11LogArg (0) (-1) (2988861339626244758173969 / 1562500000000000000000000) (2444303704937 / 1250000000000) (55696295063 / 1250000000000)
  have hratio : ((55696295063 / 1250000000000) / (2444303704937 / 1250000000000) : ℚ) = (55696295063 / 2444303704937) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X17XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X17XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X17XV11_rounded_endpoints :
    (430684095985721151472989209076285374159 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X17XV11Interval.1 ∧ manuscriptCase2X17XV11Interval.2 ≤ (861368191971442342309020170650827868703 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X17XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X17XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X17 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((430684095985721151472989209076285374159 / 5000000000000000000000000000000000000000) : ℝ) ((861368191971442342309020170650827868703 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((430684095985721151472989209076285374159 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X17XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X17XV11Interval.2 : ℝ) ≤ ((861368191971442342309020170650827868703 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X17XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X17XV11_exact_interval.1, manuscriptCase2X17XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
