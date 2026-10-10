import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX2

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X2XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (14688791483016301985809 / 10000000000000000000000) (-31525249303 / 168474750697)

private theorem manuscriptCase2X2XV7_arg_eq : barrierCase2X2XV7LogArg = barrierComplex (1 / 1) (68474750697 / 100000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV7LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV7Interval.1 : ℝ) (manuscriptCase2X2XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X2XV7LogArg).re ∈ _
  rw [manuscriptCase2X2XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X2XV7LogArg (0) (1) (14688791483016301985809 / 10000000000000000000000) (168474750697 / 100000000000) (-31525249303 / 100000000000)
  have hratio : ((-31525249303 / 100000000000) / (168474750697 / 100000000000) : ℚ) = (-31525249303 / 168474750697) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV7_rounded_endpoints :
    (-603778598638846551019228852617314516767 / 5000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV7Interval.1 ∧ manuscriptCase2X2XV7Interval.2 ≤ (-603778598638846523658995888059812586609 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-603778598638846551019228852617314516767 / 5000000000000000000000000000000000000000) : ℝ) ((-603778598638846523658995888059812586609 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-603778598638846551019228852617314516767 / 5000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV7Interval.2 : ℝ) ≤ ((-603778598638846523658995888059812586609 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV7_exact_interval.1, manuscriptCase2X2XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (-546813624097 / 3453186375903)

private theorem manuscriptCase2X2XV9_arg_eq : barrierCase2X2XV9LogArg = barrierComplex (1 / 1) (1453186375903 / 2000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV9LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV9Interval.1 : ℝ) (manuscriptCase2X2XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X2XV9LogArg).re ∈ _
  rw [manuscriptCase2X2XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X2XV9LogArg (0) (1) (6111750643110095219065409 / 4000000000000000000000000) (3453186375903 / 2000000000000) (-546813624097 / 2000000000000)
  have hratio : ((-546813624097 / 2000000000000) / (3453186375903 / 2000000000000) : ℚ) = (-546813624097 / 3453186375903) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV9_rounded_endpoints :
    (303316272309543008972323408117925651831 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV9Interval.1 ∧ manuscriptCase2X2XV9Interval.2 ≤ (303316272309543030564582506060772399829 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((303316272309543008972323408117925651831 / 10000000000000000000000000000000000000000) : ℝ) ((303316272309543030564582506060772399829 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((303316272309543008972323408117925651831 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV9Interval.2 : ℝ) ≤ ((303316272309543030564582506060772399829 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV9_exact_interval.1, manuscriptCase2X2XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X2XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (-314178407141 / 2185821592859)

private theorem manuscriptCase2X2XV11_arg_eq : barrierCase2X2XV11LogArg = barrierComplex (1 / 1) (935821592859 / 1250000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X2XV11LogArg, Case2PointData.X2, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X2XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X2XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X2XV11Interval.1 : ℝ) (manuscriptCase2X2XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X2XV11LogArg).re ∈ _
  rw [manuscriptCase2X2XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X2XV11LogArg (0) (1) (2438262053661155959793881 / 1562500000000000000000000) (2185821592859 / 1250000000000) (-314178407141 / 1250000000000)
  have hratio : ((-314178407141 / 1250000000000) / (2185821592859 / 1250000000000) : ℚ) = (-314178407141 / 2185821592859) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X2XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X2XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X2XV11_rounded_endpoints :
    (-674910811322954804040864530758684571819 / 10000000000000000000000000000000000000000) ≤ manuscriptCase2X2XV11Interval.1 ∧ manuscriptCase2X2XV11Interval.2 ≤ (-674910811322954764678520667095043747027 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X2XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X2XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X2 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-674910811322954804040864530758684571819 / 10000000000000000000000000000000000000000) : ℝ) ((-674910811322954764678520667095043747027 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-674910811322954804040864530758684571819 / 10000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X2XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X2XV11Interval.2 : ℝ) ≤ ((-674910811322954764678520667095043747027 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X2XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X2XV11_exact_interval.1, manuscriptCase2X2XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
