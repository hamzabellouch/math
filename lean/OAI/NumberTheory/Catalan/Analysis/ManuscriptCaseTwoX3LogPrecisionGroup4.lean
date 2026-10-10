import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointX3

namespace OAI

noncomputable section
namespace InternalCatalan

def manuscriptCase2X3XV7Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-7835271 / 50000000) (15094393 / 100000000) (0) (1) (3356456412894182624329 / 2500000000000000000000) (-20734723427 / 79265276573)

private theorem manuscriptCase2X3XV7_arg_eq : barrierCase2X3XV7LogArg = barrierComplex (1 / 1) (29265276573 / 50000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV7LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV7_weight_eq : (barrierV2Tail.getD 7 (0, 0)).2 = barrierComplex (-7835271 / 50000000) (15094393 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV7_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV7Interval.1 : ℝ) (manuscriptCase2X3XV7Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 7 (0, 0)).2 * Complex.log barrierCase2X3XV7LogArg).re ∈ _
  rw [manuscriptCase2X3XV7_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-7835271 / 50000000) (15094393 / 100000000)
    barrierCase2X3XV7LogArg (0) (1) (3356456412894182624329 / 2500000000000000000000) (79265276573 / 50000000000) (-20734723427 / 50000000000)
  have hratio : ((-20734723427 / 50000000000) / (79265276573 / 50000000000) : ℚ) = (-20734723427 / 79265276573) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV7Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV7_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV7_rounded_endpoints :
    (-206027747698688997926255907599841801511 / 2000000000000000000000000000000000000000) ≤ manuscriptCase2X3XV7Interval.1 ∧ manuscriptCase2X3XV7Interval.2 ≤ (-128767342311680616863851701121543371403 / 1250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV7Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV7_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 7 (0, 0)) ∈ Set.Icc ((-206027747698688997926255907599841801511 / 2000000000000000000000000000000000000000) : ℝ) ((-128767342311680616863851701121543371403 / 1250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-206027747698688997926255907599841801511 / 2000000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV7Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV7_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV7Interval.2 : ℝ) ≤ ((-128767342311680616863851701121543371403 / 1250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV7_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV7_exact_interval.1, manuscriptCase2X3XV7_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XV9Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (-3346771 / 100000000) (-5956127 / 100000000) (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (-378925797173 / 1621074202827)

private theorem manuscriptCase2X3XV9_arg_eq : barrierCase2X3XV9LogArg = barrierComplex (1 / 1) (621074202827 / 1000000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV9LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV9_weight_eq : (barrierV2Tail.getD 9 (0, 0)).2 = barrierComplex (-3346771 / 100000000) (-5956127 / 100000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV9_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV9Interval.1 : ℝ) (manuscriptCase2X3XV9Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 9 (0, 0)).2 * Complex.log barrierCase2X3XV9LogArg).re ∈ _
  rw [manuscriptCase2X3XV9_weight_eq]
  have h := manuscript_weighted_complex_log_interval (-3346771 / 100000000) (-5956127 / 100000000)
    barrierCase2X3XV9LogArg (0) (1) (1385733165417193534791929 / 1000000000000000000000000) (1621074202827 / 1000000000000) (-378925797173 / 1000000000000)
  have hratio : ((-378925797173 / 1000000000000) / (1621074202827 / 1000000000000) : ℚ) = (-378925797173 / 1621074202827) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV9Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV9_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV9_rounded_endpoints :
    (3455421114603915240691889145026748241 / 125000000000000000000000000000000000000) ≤ manuscriptCase2X3XV9Interval.1 ∧ manuscriptCase2X3XV9Interval.2 ≤ (55286737833662648169522045780175335331 / 2000000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV9Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV9_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 9 (0, 0)) ∈ Set.Icc ((3455421114603915240691889145026748241 / 125000000000000000000000000000000000000) : ℝ) ((55286737833662648169522045780175335331 / 2000000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((3455421114603915240691889145026748241 / 125000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV9Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV9_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV9Interval.2 : ℝ) ≤ ((55286737833662648169522045780175335331 / 2000000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV9_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV9_exact_interval.1, manuscriptCase2X3XV9_exact_interval.2.trans hhi⟩

def manuscriptCase2X3XV11Interval : ℚ × ℚ :=
  manuscriptWeightedComplexLogInterval (2055213 / 200000000) (21715849 / 200000000) (0) (1) (550592025563902332388561 / 390625000000000000000000) (-225041220169 / 1024958779831)

private theorem manuscriptCase2X3XV11_arg_eq : barrierCase2X3XV11LogArg = barrierComplex (1 / 1) (399958779831 / 625000000000) := by
  apply Complex.ext <;> norm_num [barrierCase2X3XV11LogArg, Case2PointData.X3, barrierV2Tail,
    barrierConjugatePair, barrierComplex, pow_two]

private theorem manuscriptCase2X3XV11_weight_eq : (barrierV2Tail.getD 11 (0, 0)).2 = barrierComplex (2055213 / 200000000) (21715849 / 200000000) := by
  apply Complex.ext <;> norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex]

theorem manuscriptCase2X3XV11_exact_interval :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc (manuscriptCase2X3XV11Interval.1 : ℝ) (manuscriptCase2X3XV11Interval.2 : ℝ) := by
  change ((barrierV2Tail.getD 11 (0, 0)).2 * Complex.log barrierCase2X3XV11LogArg).re ∈ _
  rw [manuscriptCase2X3XV11_weight_eq]
  have h := manuscript_weighted_complex_log_interval (2055213 / 200000000) (21715849 / 200000000)
    barrierCase2X3XV11LogArg (0) (1) (550592025563902332388561 / 390625000000000000000000) (1024958779831 / 625000000000) (-225041220169 / 625000000000)
  have hratio : ((-225041220169 / 625000000000) / (1024958779831 / 625000000000) : ℚ) = (-225041220169 / 1024958779831) := by norm_num
  rw [hratio] at h
  unfold manuscriptCase2X3XV11Interval
  apply h
  all_goals
    try rw [manuscriptCase2X3XV11_arg_eq]
    try apply Complex.ext
    all_goals norm_num [barrierComplex, barrierOctantRotate, barrierOctantMultiplier, pow_two]

theorem manuscriptCase2X3XV11_rounded_endpoints :
    (-150117266368054083110122305598162229591 / 2500000000000000000000000000000000000000) ≤ manuscriptCase2X3XV11Interval.1 ∧ manuscriptCase2X3XV11Interval.2 ≤ (-15011726636805407326953633996529959089 / 250000000000000000000000000000000000000) := by
  simp only [manuscriptCase2X3XV11Interval, manuscriptWeightedComplexLogInterval,
    manuscriptIntervalAdd, manuscriptIntervalScale, manuscriptScaledLogInterval,
    manuscriptLogHInterval, manuscriptArgInterval, manuscriptPiQuarterInterval,
    manuscriptAtanInterval, barrierLogHRat_two_eq,
    barrierAtanJRat_half_eq, barrierAtanJRat_third_eq]
  decide +kernel

theorem manuscriptCase2X3XV11_enclosure :
    barrierCase2XVLogTerm (Case2PointData.X3 : ℝ) (barrierV2Tail.getD 11 (0, 0)) ∈ Set.Icc ((-150117266368054083110122305598162229591 / 2500000000000000000000000000000000000000) : ℝ) ((-15011726636805407326953633996529959089 / 250000000000000000000000000000000000000) : ℝ) := by
  have hlo : ((-150117266368054083110122305598162229591 / 2500000000000000000000000000000000000000) : ℝ) ≤ (manuscriptCase2X3XV11Interval.1 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV11_rounded_endpoints.1
  have hhi : (manuscriptCase2X3XV11Interval.2 : ℝ) ≤ ((-15011726636805407326953633996529959089 / 250000000000000000000000000000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr manuscriptCase2X3XV11_rounded_endpoints.2
  exact ⟨hlo.trans manuscriptCase2X3XV11_exact_interval.1, manuscriptCase2X3XV11_exact_interval.2.trans hhi⟩

end InternalCatalan

end

end OAI
