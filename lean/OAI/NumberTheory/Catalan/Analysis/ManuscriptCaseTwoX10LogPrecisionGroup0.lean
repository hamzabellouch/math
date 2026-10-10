import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX10Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X10XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (0) (0) (18774036720077580235849 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X10XP0_arg_eq : barrierCase2X10XP0LogArg = barrierComplex (137018380957 / 100000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XP0LogArg, Case2PointData.X10, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XP0Interval.1 : ℝ) (manuscriptCase2X10XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X10XP0LogArg).re ∈ _
  rw [manuscriptCase2X10XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X10XP0LogArg (0) (0) (18774036720077580235849 / 10000000000000000000000) (137018380957 / 100000000000) (0 / 1)
  have hratio : ((0 / 1) / (137018380957 / 100000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XP0_rounded_endpoints :
    (-117643912657759339846276391415198481731 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X10XP0Interval.1 ∧ manuscriptCase2X10XP0Interval.2 ≤ (-294109781644398349613401127123193655523 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-117643912657759339846276391415198481731 / 2000000000000000000000000000000000000000) : ℝ) ((-294109781644398349613401127123193655523 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-117643912657759339846276391415198481731 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XP0Interval.2 : ℝ) ≤ ((-294109781644398349613401127123193655523 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XP0_exact_interval.1, manuscriptCase2X10XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (1) (0) (139498466909137279034569 / 125000000000000000000000) (0 / 1)

private theorem manuscriptCase2X10XP1_arg_eq : barrierCase2X10XP1LogArg = barrierComplex (373494935587 / 250000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XP1LogArg, Case2PointData.X10, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XP1Interval.1 : ℝ) (manuscriptCase2X10XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X10XP1LogArg).re ∈ _
  rw [manuscriptCase2X10XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X10XP1LogArg (1) (0) (139498466909137279034569 / 125000000000000000000000) (373494935587 / 250000000000) (0 / 1)
  have hratio : ((0 / 1) / (373494935587 / 250000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XP1_rounded_endpoints :
    (-42984746333094219776825949070889171789 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X10XP1Interval.1 ∧ manuscriptCase2X10XP1Interval.2 ≤ (-171938985332376879078382731829573432521 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-42984746333094219776825949070889171789 / 2500000000000000000000000000000000000000) : ℝ) ((-171938985332376879078382731829573432521 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-42984746333094219776825949070889171789 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XP1Interval.2 : ℝ) ≤ ((-171938985332376879078382731829573432521 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XP1_exact_interval.1, manuscriptCase2X10XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X10XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (860707031277380386009 / 625000000000000000000) (10992862747 / 40007137253)

private theorem manuscriptCase2X10XP2_arg_eq : barrierCase2X10XP2LogArg = barrierComplex (51 / 100) (-14507137253 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X10XP2LogArg, Case2PointData.X10, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X10XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X10XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X10XP2Interval.1 : ℝ) (manuscriptCase2X10XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X10XP2LogArg).re ∈ _
  rw [manuscriptCase2X10XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X10XP2LogArg (-2) (-1) (860707031277380386009 / 625000000000000000000) (40007137253 / 50000000000) (10992862747 / 50000000000)
  have hratio : ((10992862747 / 50000000000) / (40007137253 / 50000000000) : ℚ) = (10992862747 / 40007137253) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X10XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X10XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X10XP2_rounded_endpoints :
    (16199932457074877392193813927275506289 / 31250000000000000000000000000000000000) ≤ manuscriptCase2X10XP2Interval.1 ∧ manuscriptCase2X10XP2Interval.2 ≤ (5183978386263960882068998352234741825643 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X10XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X10XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X10 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((16199932457074877392193813927275506289 / 31250000000000000000000000000000000000) : ℝ) ((5183978386263960882068998352234741825643 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((16199932457074877392193813927275506289 / 31250000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X10XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X10XP2Interval.2 : ℝ) ≤ ((5183978386263960882068998352234741825643 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X10XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X10XP2_exact_interval.1, manuscriptCase2X10XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
