import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX8

namespace OAI


noncomputable section
namespace InternalCatalan

def manuscriptCase2X8XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (0) (159449020859600746489 / 156250000000000000000) (1788580683 / 12500000000)

private theorem manuscriptCase2X8XV7_arg_eq : barrierCase2X8XV7LogArg = barrierComplex (1 / 1) (1788580683 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV7LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV7Interval.1 : ℝ) (manuscriptCase2X8XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X8XV7LogArg).re ∈ _
  rw [manuscriptCase2X8XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X8XV7LogArg (0) (0) (159449020859600746489 / 156250000000000000000) (1 / 1) (1788580683 / 12500000000)
  have hratio : ((1788580683 / 12500000000) / (1 / 1) : ℚ) = (1788580683 / 12500000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV7_rounded_endpoints :
    (-57600976261519263958727768186817001339 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X8XV7Interval.1 ∧ manuscriptCase2X8XV7Interval.2 ≤ (-46080781009215411166982214549453601071 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-57600976261519263958727768186817001339 / 2500000000000000000000000000000000000000) : ℝ) ((-46080781009215411166982214549453601071 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-57600976261519263958727768186817001339 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV7Interval.2 : ℝ) ≤ ((-46080781009215411166982214549453601071 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV7_exact_interval.1, manuscriptCase2X8XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (0) (63940783703445615218089 / 62500000000000000000000) (37957656717 / 250000000000)

private theorem manuscriptCase2X8XV9_arg_eq : barrierCase2X8XV9LogArg = barrierComplex (1 / 1) (37957656717 / 250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV9LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV9Interval.1 : ℝ) (manuscriptCase2X8XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X8XV9LogArg).re ∈ _
  rw [manuscriptCase2X8XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X8XV9LogArg (0) (0) (63940783703445615218089 / 62500000000000000000000) (1 / 1) (37957656717 / 250000000000)
  have hratio : ((37957656717 / 250000000000) / (1 / 1) : ℚ) = (37957656717 / 250000000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV9_rounded_endpoints :
    (42966510615815023950883379382495662429 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X8XV9Interval.1 ∧ manuscriptCase2X8XV9Interval.2 ≤ (85933021231630047901766758764991324859 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((42966510615815023950883379382495662429 / 5000000000000000000000000000000000000000) : ℝ) ((85933021231630047901766758764991324859 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((42966510615815023950883379382495662429 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV9Interval.2 : ℝ) ≤ ((85933021231630047901766758764991324859 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV9_exact_interval.1, manuscriptCase2X8XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X8XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (0) (25011568507220983872001 / 24414062500000000000000) (24443936001 / 156250000000)

private theorem manuscriptCase2X8XV11_arg_eq : barrierCase2X8XV11LogArg = barrierComplex (1 / 1) (24443936001 / 156250000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X8XV11LogArg, Case2PointData.X8, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X8XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X8XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X8XV11Interval.1 : ℝ) (manuscriptCase2X8XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X8XV11LogArg).re ∈ _
  rw [manuscriptCase2X8XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X8XV11LogArg (0) (0) (25011568507220983872001 / 24414062500000000000000) (1 / 1) (24443936001 / 156250000000)
  have hratio : ((24443936001 / 156250000000) / (1 / 1) : ℚ) = (24443936001 / 156250000000) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X8XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X8XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X8XV11_rounded_endpoints :
    (-167254598846487950517714079846723396807 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X8XV11Interval.1 ∧ manuscriptCase2X8XV11Interval.2 ≤ (-83627299423243975258857039923361698403 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X8XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X8XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X8 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-167254598846487950517714079846723396807 / 10000000000000000000000000000000000000000) : ℝ) ((-83627299423243975258857039923361698403 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-167254598846487950517714079846723396807 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X8XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X8XV11Interval.2 : ℝ) ≤ ((-83627299423243975258857039923361698403 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X8XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X8XV11_exact_interval.1, manuscriptCase2X8XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
