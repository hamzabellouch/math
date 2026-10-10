import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointY2

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2Y2YV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (7835271 / 50000000) (-15094393 / 100000000) (-5) (-1) (34411846461522144961 / 19531250000000000000) (68826949 / 431173051)

private theorem manuscriptCase2Y2YV7_arg_eq : barrierCase2Y2YV7LogArg = barrierComplex (19 / 100) (-3442287969 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV7LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV7_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) = barrierComplex (7835271 / 50000000) (-15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV7_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV7Interval.1 : ℝ) (manuscriptCase2Y2YV7Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 7 (0, 0)).2) * Complex.log barrierCase2Y2YV7LogArg).re ∈ _
  rw [manuscriptCase2Y2YV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (7835271 / 50000000) (-15094393 / 100000000)
    barrierCase2Y2YV7LogArg (-5) (-1) (34411846461522144961 / 19531250000000000000) (8192287969 / 25000000000) (1307712031 / 25000000000)
  have hratio : ((1307712031 / 25000000000) / (8192287969 / 25000000000) : ℚ) = (68826949 / 431173051) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV7_rounded_endpoints :
    (-3218298964859688060024190663413211935743 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV7Interval.1 ∧ manuscriptCase2Y2YV7Interval.2 ≤ (-10057184265186525014920486666762718801 / 31250000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV7_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-3218298964859688060024190663413211935743 / 10000000000000000000000000000000000000000) : ℝ) ((-10057184265186525014920486666762718801 / 31250000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-3218298964859688060024190663413211935743 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV7_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV7Interval.2 : ℝ) ≤ ((-10057184265186525014920486666762718801 / 31250000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV7_exact_interval.1, manuscriptCase2Y2YV7_exact_interval.2.trans hhi⟩

def manuscriptCase2Y2YV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (3346771 / 100000000) (5956127 / 100000000) (-6) (-1) (7271640999000486053361 / 3906250000000000000000) (-9688500077 / 39013500077)

private theorem manuscriptCase2Y2YV9_arg_eq : barrierCase2Y2YV9LogArg = barrierComplex (3519 / 40000) (-73053000231 / 500000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV9LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV9_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) = barrierComplex (3346771 / 100000000) (5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV9_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV9Interval.1 : ℝ) (manuscriptCase2Y2YV9Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 9 (0, 0)).2) * Complex.log barrierCase2Y2YV9LogArg).re ∈ _
  rw [manuscriptCase2Y2YV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (3346771 / 100000000) (5956127 / 100000000)
    barrierCase2Y2YV9LogArg (-6) (-1) (7271640999000486053361 / 3906250000000000000000) (117040500231 / 500000000000) (-29065500231 / 500000000000)
  have hratio : ((-29065500231 / 500000000000) / (117040500231 / 500000000000) : ℚ) = (-9688500077 / 39013500077) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV9_rounded_endpoints :
    (10408195292627299616232084999787794639 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV9Interval.1 ∧ manuscriptCase2Y2YV9Interval.2 ≤ (10408195292627310480414471884749588967 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV9_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((10408195292627299616232084999787794639 / 5000000000000000000000000000000000000000) : ℝ) ((10408195292627310480414471884749588967 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((10408195292627299616232084999787794639 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV9_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV9Interval.2 : ℝ) ≤ ((10408195292627310480414471884749588967 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV9_exact_interval.1, manuscriptCase2Y2YV9_exact_interval.2.trans hhi⟩

def manuscriptCase2Y2YV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2055213 / 200000000) (-21715849 / 200000000) (-6) (-2) (2311601000202080631049 / 1525878906250000000000) (9920000000 / 47044602243)

private theorem manuscriptCase2Y2YV11_arg_eq : barrierCase2Y2YV11LogArg = barrierComplex (496 / 15625) (-47044602243 / 312500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2Y2YV11LogArg, Case2PointData.Y2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2Y2YV11_weight_eq : ((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) = barrierComplex (-2055213 / 200000000) (-21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2Y2YV11_exact_interval :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2Y2YV11Interval.1 : ℝ) (manuscriptCase2Y2YV11Interval.2 : ℝ) := by
  change (((-1 : ℂ) * (barrierV2Tail.getD 11 (0, 0)).2) * Complex.log barrierCase2Y2YV11LogArg).re ∈ _
  rw [manuscriptCase2Y2YV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2055213 / 200000000) (-21715849 / 200000000)
    barrierCase2Y2YV11LogArg (-6) (-2) (2311601000202080631049 / 1525878906250000000000) (47044602243 / 156250000000) (992 / 15625)
  have hratio : ((992 / 15625) / (47044602243 / 156250000000) : ℚ) = (9920000000 / 47044602243) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2Y2YV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2Y2YV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2Y2YV11_rounded_endpoints :
    (-1287567243325205355081645451901291656767 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2Y2YV11Interval.1 ∧ manuscriptCase2Y2YV11Interval.2 ≤ (-51502689733008211052612970816028183113 / 400000000000000000000000000000000000000) := by
  simp only [manuscriptCase2Y2YV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2Y2YV11_enclosure :
    barrierCase2YVLogTerm (Case2PointData.Y2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-1287567243325205355081645451901291656767 / 10000000000000000000000000000000000000000) : ℝ) ((-51502689733008211052612970816028183113 / 400000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-1287567243325205355081645451901291656767 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2Y2YV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV11_rounded_endpoints.1
  have hhi : (manuscriptCase2Y2YV11Interval.2 : ℝ) ≤ ((-51502689733008211052612970816028183113 / 400000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2Y2YV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2Y2YV11_exact_interval.1, manuscriptCase2Y2YV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
