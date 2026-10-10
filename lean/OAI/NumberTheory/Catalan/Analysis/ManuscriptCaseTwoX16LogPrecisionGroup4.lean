import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX16

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X16XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (-1) (1065932078913436107361 / 625000000000000000000) (4001617231 / 45998382769)

private theorem manuscriptCase2X16XV7_arg_eq : barrierCase2X16XV7LogArg = barrierComplex (1 / 1) (-20998382769 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XV7LogArg, Case2PointData.X16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XV7Interval.1 : ℝ) (manuscriptCase2X16XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X16XV7LogArg).re ∈ _
  rw [manuscriptCase2X16XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X16XV7LogArg (0) (-1) (1065932078913436107361 / 625000000000000000000) (45998382769 / 25000000000) (4001617231 / 25000000000)
  have hratio : ((4001617231 / 25000000000) / (45998382769 / 25000000000) : ℚ) = (4001617231 / 45998382769) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XV7_rounded_endpoints :
    (636238866892745005013626137545005794689 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X16XV7Interval.1 ∧ manuscriptCase2X16XV7Interval.2 ≤ (79529858361593132466762938728949623213 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((636238866892745005013626137545005794689 / 10000000000000000000000000000000000000000) : ℝ) ((79529858361593132466762938728949623213 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((636238866892745005013626137545005794689 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XV7Interval.2 : ℝ) ≤ ((79529858361593132466762938728949623213 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XV7_exact_interval.1, manuscriptCase2X16XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (-1) (448588187294334106575761 / 250000000000000000000000) (54367654569 / 945632345431)

private theorem manuscriptCase2X16XV9_arg_eq : barrierCase2X16XV9LogArg = barrierComplex (1 / 1) (-445632345431 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XV9LogArg, Case2PointData.X16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XV9Interval.1 : ℝ) (manuscriptCase2X16XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X16XV9LogArg).re ∈ _
  rw [manuscriptCase2X16XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X16XV9LogArg (0) (-1) (448588187294334106575761 / 250000000000000000000000) (945632345431 / 500000000000) (54367654569 / 500000000000)
  have hratio : ((54367654569 / 500000000000) / (945632345431 / 500000000000) : ℚ) = (54367654569 / 945632345431) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XV9_rounded_endpoints :
    (-531420496539105283179152972939928127667 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X16XV9Interval.1 ∧ manuscriptCase2X16XV9Interval.2 ≤ (-106284099307821052317366693113951286523 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((-531420496539105283179152972939928127667 / 10000000000000000000000000000000000000000) : ℝ) ((-106284099307821052317366693113951286523 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-531420496539105283179152972939928127667 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XV9Interval.2 : ℝ) ≤ ((-106284099307821052317366693113951286523 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XV9_exact_interval.1, manuscriptCase2X16XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X16XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (-1) (180012563850387344052649 / 97656250000000000000000) (25522102157 / 599477897843)

private theorem manuscriptCase2X16XV11_arg_eq : barrierCase2X16XV11LogArg = barrierComplex (1 / 1) (-286977897843 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X16XV11LogArg, Case2PointData.X16, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X16XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X16XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X16XV11Interval.1 : ℝ) (manuscriptCase2X16XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X16XV11LogArg).re ∈ _
  rw [manuscriptCase2X16XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X16XV11LogArg (0) (-1) (180012563850387344052649 / 97656250000000000000000) (599477897843 / 312500000000) (25522102157 / 312500000000)
  have hratio : ((25522102157 / 312500000000) / (599477897843 / 312500000000) : ℚ) = (25522102157 / 599477897843) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X16XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X16XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X16XV11_rounded_endpoints :
    (838003712399578291928064556655763083031 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X16XV11Interval.1 ∧ manuscriptCase2X16XV11Interval.2 ≤ (419001856199789165645249174002967384491 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X16XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X16XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X16 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((838003712399578291928064556655763083031 / 10000000000000000000000000000000000000000) : ℝ) ((419001856199789165645249174002967384491 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((838003712399578291928064556655763083031 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X16XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X16XV11Interval.2 : ℝ) ≤ ((419001856199789165645249174002967384491 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X16XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X16XV11_exact_interval.1, manuscriptCase2X16XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
