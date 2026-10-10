import OAI.Probability.SATComputability.TrialDescriptions

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open PeriodicLattice.CertifiedReal RapidForcing.EffectiveArithmetic
open scoped NNReal
local instance effectiveTrialValuesRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

abbrev TrialData := ℚ × ℕ × Code × List ℚ

noncomputable def guardedSiteExpression (t : TrialData) (k : ℕ) : Code :=
  if positiveExponents t.2.2.2 then
    averagedSiteExpression (t.2.1 : ℚ) t.2.2.1 t.2.2.2 k else .zero

attribute [local irreducible] averagedSiteExpression averagedEdgeExpression positiveExponents

@[fun_prop] theorem guardedSiteExpression_computable :
    Computable (fun p : TrialData × ℕ => guardedSiteExpression p.1 p.2) := by
  have he : Computable (fun p : TrialData × ℕ =>
      averagedSiteExpression (p.1.2.1 : ℚ) p.1.2.2.1 p.1.2.2.2 p.2) :=
    averagedSiteExpression_computable.comp
      (g := fun p : TrialData × ℕ => (((p.1.2.1 : ℚ),p.1.2.2.1,p.1.2.2.2),p.2))
      (by fun_prop)
  unfold guardedSiteExpression
  fun_prop

noncomputable def guardedSiteValue (t : TrialData) (k : ℕ) : ℝ :=
  expressionValue (guardedSiteExpression t k)

theorem guardedSiteValue_effective : Effective (fun p : TrialData × ℕ => guardedSiteValue p.1 p.2) :=
  expressionValue_effective.comp guardedSiteExpression_computable

theorem guardedSiteValue_bound (t : TrialData) (k : ℕ) :
    |guardedSiteValue t k| ≤ (t.2.1 : ℝ)*((k : ℝ)+1) := by
  unfold guardedSiteValue guardedSiteExpression
  split_ifs with h
  · have hp := (positiveExponents_iff t.2.2.2).mp h
    apply (packetSiteValue_bound (β := (t.2.1 : ℚ)) (by positivity)
      t.2.2.1 t.2.2.2 hp k).trans
    push_cast
    nlinarith [show (0 : ℝ) ≤ t.2.1 from Nat.cast_nonneg _]
  · simp only [expressionValue, abs_zero]
    positivity

noncomputable def trialRate (t : TrialData) : ℚ := 3 * max 0 t.1

@[fun_prop] theorem trialRate_computable : Computable trialRate := by
  unfold trialRate
  fun_prop

theorem trialRate_nonneg (t : TrialData) : 0 ≤ trialRate t := by
  unfold trialRate
  positivity

noncomputable def trialDensityNN (t : TrialData) : ℝ≥0 :=
  ⟨(max 0 t.1 : ℚ), by exact_mod_cast le_max_left (0 : ℚ) t.1⟩

noncomputable def trialValue (t : TrialData) : ℝ :=
  Real.log 2 +
    (∫ k, guardedSiteValue t k ∂poissonMeasure (trialDensityNN t * 3)) -
      2*(max 0 t.1 : ℚ)*packetEdgeValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2

attribute [local irreducible] guardedSiteValue packetEdgeValue

private theorem siteExpectation_effective : Effective (fun t : TrialData =>
    ∫ k, guardedSiteValue t k ∂poissonMeasure (trialDensityNN t * 3)) := by
  have hs := effective_poisson_expectation trialRate trialRate_computable trialRate_nonneg
    (fun t : TrialData => t.2.1) (by fun_prop) guardedSiteValue
    guardedSiteValue_effective guardedSiteValue_bound
  convert hs using 1
  funext t
  congr 1
  congr 1
  apply Subtype.ext
  change ((max 0 t.1 : ℚ) : ℝ)*3 = ((3*max 0 t.1 : ℚ) : ℝ)
  push_cast
  ring

private theorem edgePacket_effective :
    Effective (fun t : TrialData => packetEdgeValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2) := by
  simpa only [packetEdgeValue] using expressionValue_effective.comp
    (averagedEdgeExpression_computable.comp
      (g := fun t : TrialData => ((t.2.1 : ℚ),t.2.2.1,t.2.2.2)) (by fun_prop))

theorem trialValue_effective : Effective trialValue := by
  have hlog : Effective (fun _t : TrialData => Real.log 2) :=
    (rational (Computable.const (2 : ℚ))).log (fun _ => by norm_num)
  have ha : Effective (fun t : TrialData => ((2*(max 0 t.1) : ℚ) : ℝ)) :=
    rational (by fun_prop)
  apply ((hlog.add siteExpectation_effective).sub (ha.mul edgePacket_effective)).congr
  intro t
  simp only [trialValue, Rat.cast_mul, Rat.cast_ofNat]

theorem trialValue_eq_functional (t : TrialData)
    (hm : exponentCheck t.2.2.2 = true) :
    trialValue t = functional (satModel (trialDensityNN t) (t.2.1 : ℝ)) t.2.2.2.length
      (rationalTreeValue (t.2.2.2.length+1) (decodeTree (t.2.2.2.length+1) t.2.2.1))
      (fun i => (t.2.2.2.get i : ℝ)) := by
  have hp := exponentCheck_positive hm
  have he (k : ℕ) : guardedSiteValue t k = packetSiteValue (t.2.1 : ℚ) t.2.2.1 t.2.2.2 k := by
    simp only [guardedSiteValue, guardedSiteExpression, hp, ite_true, packetSiteValue]
  have hf := packet_functional (trialDensityNN t) (t.2.1 : ℚ) t.2.2.1 t.2.2.2
    ((positiveExponents_iff _).mp hp)
  simp only [Rat.cast_natCast] at hf
  rw [hf]
  have hc : (trialDensityNN t : ℝ) = (max 0 t.1 : ℚ) := rfl
  simp only [trialValue, he, hc]
  push_cast
  ring

end FixedClauseThreshold.Computability

end OAI
