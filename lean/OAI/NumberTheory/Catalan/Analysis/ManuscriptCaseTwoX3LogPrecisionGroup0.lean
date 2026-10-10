import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoLogsX3Group0

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X3XP0Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2334613 / 12500000) (0 / 1) (2) (0) (19995050420684000351001 / 10000000000000000000000) (0 / 1)

private theorem manuscriptCase2X3XP0_arg_eq : barrierCase2X3XP0LogArg = barrierComplex (141403855749 / 50000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XP0LogArg, Case2PointData.X3, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XP0_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 = barrierComplex (-2334613 / 12500000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XP0_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XP0Interval.1 : ℝ) (manuscriptCase2X3XP0Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 0 (0, 0)).2 * Complex.log barrierCase2X3XP0LogArg).re ∈ _
  rw [manuscriptCase2X3XP0_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2334613 / 12500000) (0 / 1)
    barrierCase2X3XP0LogArg (2) (0) (19995050420684000351001 / 10000000000000000000000) (141403855749 / 50000000000) (0 / 1)
  have hratio : ((0 / 1) / (141403855749 / 50000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XP0Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XP0_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XP0_rounded_endpoints :
    (-242705670841527036492785784887453604243 / 1250000000000000000000000000000000000000) ≤ manuscriptCase2X3XP0Interval.1 ∧ manuscriptCase2X3XP0Interval.2 ≤ (-1941645366732216291565480246824150361259 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XP0Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XP0_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 0 (0, 0)) ∈ Set.Icc ((-242705670841527036492785784887453604243 / 1250000000000000000000000000000000000000) : ℝ) ((-1941645366732216291565480246824150361259 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-242705670841527036492785784887453604243 / 1250000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XP0Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP0_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XP0Interval.2 : ℝ) ≤ ((-1941645366732216291565480246824150361259 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP0_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XP0_exact_interval.1, manuscriptCase2X3XP0_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XP1Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-2141509 / 50000000) (0 / 1) (3) (0) (150761185738922475520281 / 125000000000000000000000) (0 / 1)

private theorem manuscriptCase2X3XP1_arg_eq : barrierCase2X3XP1LogArg = barrierComplex (388279777659 / 125000000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XP1LogArg, Case2PointData.X3, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XP1_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 = barrierComplex (-2141509 / 50000000) (0 / 1) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XP1_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XP1Interval.1 : ℝ) (manuscriptCase2X3XP1Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 1 (0, 0)).2 * Complex.log barrierCase2X3XP1LogArg).re ∈ _
  rw [manuscriptCase2X3XP1_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-2141509 / 50000000) (0 / 1)
    barrierCase2X3XP1LogArg (3) (0) (150761185738922475520281 / 125000000000000000000000) (388279777659 / 125000000000) (0 / 1)
  have hratio : ((0 / 1) / (388279777659 / 125000000000) : ℚ) = (0 / 1) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XP1Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XP1_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XP1_rounded_endpoints :
    (-48544257916192874307207849974287292703 / 1000000000000000000000000000000000000000) ≤ manuscriptCase2X3XP1Interval.1 ∧ manuscriptCase2X3XP1Interval.2 ≤ (-485442579161928742985315306380923163127 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XP1Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XP1_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 1 (0, 0)) ∈ Set.Icc ((-48544257916192874307207849974287292703 / 1000000000000000000000000000000000000000) : ℝ) ((-485442579161928742985315306380923163127 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-48544257916192874307207849974287292703 / 1000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XP1Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP1_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XP1Interval.2 : ℝ) ≤ ((-485442579161928742985315306380923163127 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP1_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XP1_exact_interval.1, manuscriptCase2X3XP1_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XP2Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-33138961 / 50000000) (31907569 / 100000000) (0) (1) (680665762121172204841 / 625000000000000000000) (10011881779 / 35511881779)

private theorem manuscriptCase2X3XP2_arg_eq : barrierCase2X3XP2LogArg = barrierComplex (51 / 100) (22761881779 / 25000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XP2LogArg, Case2PointData.X3, barrierP2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XP2_weight_eq : (2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 = barrierComplex (-33138961 / 50000000) (31907569 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XP2_exact_interval :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XP2Interval.1 : ℝ) (manuscriptCase2X3XP2Interval.2 : ℝ) := by
  change ((2 : ℂ) * (barrierP2Tail.getD 2 (0, 0)).2 * Complex.log barrierCase2X3XP2LogArg).re ∈ _
  rw [manuscriptCase2X3XP2_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-33138961 / 50000000) (31907569 / 100000000)
    barrierCase2X3XP2LogArg (0) (1) (680665762121172204841 / 625000000000000000000) (35511881779 / 25000000000) (10011881779 / 25000000000)
  have hratio : ((10011881779 / 25000000000) / (35511881779 / 25000000000) : ℚ) = (10011881779 / 35511881779) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XP2Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XP2_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XP2_rounded_endpoints :
    (-733113748522642335058490992797000294311 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X3XP2Interval.1 ∧ manuscriptCase2X3XP2Interval.2 ≤ (-3665568742613211559620559953455884505703 / 10000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XP2Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XP2_enclosure :
    barrierCase2XPLogTerm (Case2PointData.X3 : ℝ) (barrierP2Tail.getD 2 (0, 0)) ∈ Set.Icc ((-733113748522642335058490992797000294311 / 2000000000000000000000000000000000000000) : ℝ) ((-3665568742613211559620559953455884505703 / 10000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-733113748522642335058490992797000294311 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XP2Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP2_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XP2Interval.2 : ℝ) ≤ ((-3665568742613211559620559953455884505703 / 10000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XP2_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XP2_exact_interval.1, manuscriptCase2X3XP2_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
