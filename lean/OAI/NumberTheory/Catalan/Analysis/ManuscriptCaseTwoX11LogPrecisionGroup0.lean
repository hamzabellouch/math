import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX11Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X11XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (0) (0) (865989965350797598249 / 625000000000000000000) (0 / 1)

private theorem manuscriptCase2X11XP0_arg_eq : barrierCase2X11XP0LogArg = barrierComplex (29427707443 / 25000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XP0LogArg, Case2PointData.X11, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XP0Interval.1 : ℝ) (manuscriptCase2X11XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X11XP0LogArg).re ∈ _
  rw [manuscriptCase2X11XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X11XP0LogArg (0) (0) (865989965350797598249 / 625000000000000000000) (29427707443 / 25000000000) (0 / 1)
  have hratio : ((0 / 1) / (29427707443 / 25000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XP0_rounded_endpoints :
    (-76136789364188616612511034422845021957 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X11XP0Interval.1 ∧ manuscriptCase2X11XP0Interval.2 ≤ (-152273578728377233225022068845555468237 / 5000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-76136789364188616612511034422845021957 / 2500000000000000000000000000000000000000) : ℝ) ((-152273578728377233225022068845555468237 / 5000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-76136789364188616612511034422845021957 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XP0Interval.2 : ℝ) ≤ ((-152273578728377233225022068845555468237 / 5000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XP0_exact_interval.1, manuscriptCase2X11XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (0) (0) (6404610240027706468969 / 3906250000000000000000) (0 / 1)

private theorem manuscriptCase2X11XP1_arg_eq : barrierCase2X11XP1LogArg = barrierComplex (80028808813 / 62500000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XP1LogArg, Case2PointData.X11, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XP1Interval.1 : ℝ) (manuscriptCase2X11XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X11XP1LogArg).re ∈ _
  rw [manuscriptCase2X11XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X11XP1LogArg (0) (0) (6404610240027706468969 / 3906250000000000000000) (80028808813 / 62500000000) (0 / 1)
  have hratio : ((0 / 1) / (80028808813 / 62500000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XP1_rounded_endpoints :
    (-3308900743522813714781454907966612423 / 312500000000000000000000000000000000000) ≤ manuscriptCase2X11XP1Interval.1 ∧ manuscriptCase2X11XP1Interval.2 ≤ (-13235602974091254859125794042404148829 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-3308900743522813714781454907966612423 / 312500000000000000000000000000000000000) : ℝ) ((-13235602974091254859125794042404148829 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-3308900743522813714781454907966612423 / 312500000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XP1Interval.2 : ℝ) ≤ ((-13235602974091254859125794042404148829 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XP1_exact_interval.1, manuscriptCase2X11XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X11XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (-2) (-1) (72161285330618364409 / 39062500000000000000) (44745509 / 705254491)

private theorem manuscriptCase2X11XP2_arg_eq : barrierCase2X11XP2LogArg = barrierComplex (51 / 100) (-5614326347 / 12500000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X11XP2LogArg, Case2PointData.X11, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X11XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X11XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X11XP2Interval.1 : ℝ) (manuscriptCase2X11XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X11XP2LogArg).re ∈ _
  rw [manuscriptCase2X11XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X11XP2LogArg (-2) (-1) (72161285330618364409 / 39062500000000000000) (11989326347 / 12500000000) (760673653 / 12500000000)
  have hratio : ((760673653 / 12500000000) / (11989326347 / 12500000000) : ℚ) = (44745509 / 705254491) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X11XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X11XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X11XP2_rounded_endpoints :
    (486400749589225572137497060986627412291 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X11XP2Interval.1 ∧ manuscriptCase2X11XP2Interval.2 ≤ (304000468493265989871782033356928552061 / 625000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X11XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X11XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X11 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((486400749589225572137497060986627412291 / 1000000000000000000000000000000000000000) : ℝ) ((304000468493265989871782033356928552061 / 625000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((486400749589225572137497060986627412291 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X11XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X11XP2Interval.2 : ℝ) ≤ ((304000468493265989871782033356928552061 / 625000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X11XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X11XP2_exact_interval.1, manuscriptCase2X11XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
