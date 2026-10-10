import OAI.Combinatorics.EditApproximation.Refinement.PhysicalExpectedRegret

namespace OAI

/-!
# Parent random streams in a fixed child environment

Finite parent arrays contain independent uniform optimizer integers and
actual shared-group draws. The projection laws are exact. Their use in the
node bound needs only the individual marginals, so no independence between
an online payoff and a group-failure indicator is asserted there.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

abbrev ParentGroupDraw (M K : ℕ) (count : Fin K → ℕ) :=
  ∀ scale : Fin K, Fin (count scale) → Fin M

abbrev ParentRandomSpace (R O M K : ℕ) (count : Fin K → ℕ) :=
  (Fin R → Fin O) × (Fin R → ParentGroupDraw M K count)

noncomputable def parentDrawLaw (R O M K : ℕ) [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (count : Fin K → ℕ) :
    Measure (ParentRandomSpace R O M K count) :=
  (Measure.pi fun _ : Fin R => (PMF.uniformOfFintype (Fin O)).toMeasure).prod
    (Measure.pi fun _ : Fin R => groupSharedDrawLaw (M := M) count)

instance parentDrawLaw_probability (R O M K : ℕ) [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (count : Fin K → ℕ) :
    IsProbabilityMeasure (parentDrawLaw R O M K count) := by
  dsimp only [parentDrawLaw]
  infer_instance

def parentOnlineDraw {R O M K : ℕ} [NeZero R] {count : Fin K → ℕ}
    (ω : ParentRandomSpace R O M K count) (t : ℕ) : Fin O := ω.1 (Fin.ofNat R t)

def parentGroupDraw {R O M K : ℕ} [NeZero R] {count : Fin K → ℕ}
    (ω : ParentRandomSpace R O M K count) (t : ℕ) : ParentGroupDraw M K count := ω.2 (Fin.ofNat R t)

theorem parentDrawLaw_online_mean (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (t : ℕ) (payoff : Fin O → ℝ) :
    (∫ ω, payoff (parentOnlineDraw ω t) ∂parentDrawLaw R O M K count) = uniformMean payoff := by
  unfold parentOnlineDraw parentDrawLaw
  rw [integral_fun_fst (fun array : Fin R → Fin O => payoff (array (Fin.ofNat R t))), probReal_univ, one_smul, integral_comp_eval
    (μ := fun _ : Fin R => (PMF.uniformOfFintype (Fin O)).toMeasure)
    (i := Fin.ofNat R t) (f := payoff) (measurable_of_finite _).aestronglyMeasurable]
  exact uniform_integral payoff

theorem parentDrawLaw_group_mean (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (t : ℕ) (payoff : ParentGroupDraw M K count → ℝ) :
    (∫ ω, payoff (parentGroupDraw ω t) ∂parentDrawLaw R O M K count) =
      ∫ draw, payoff draw ∂groupSharedDrawLaw (M := M) count := by
  unfold parentGroupDraw parentDrawLaw
  rw [integral_fun_snd (fun array : Fin R → ParentGroupDraw M K count => payoff (array (Fin.ofNat R t))), probReal_univ, one_smul, integral_comp_eval
    (μ := fun _ : Fin R => groupSharedDrawLaw (M := M) count)
    (i := Fin.ofNat R t) (f := payoff) (measurable_of_finite _).aestronglyMeasurable]

/-- A finite Boolean event has precisely its probability as expected indicator. -/
theorem bool_indicator_integral {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) (failure : Ω → Bool) :
    (∫ ω, (if failure ω then (1 : ℝ) else 0) ∂μ) = μ.real {ω | failure ω = true} := by
  have hmeas : MeasurableSet {ω | failure ω = true} := Set.toFinite _ |>.measurableSet
  simpa only [Set.indicator, Pi.one_apply, Set.mem_ofPred_eq] using
    (integral_indicator_one (μ := μ) hmeas)


theorem parentDrawLaw_group_failure_mean (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (t : ℕ) (failure : ParentGroupDraw M K count → Bool) :
    (∫ ω, (if failure (parentGroupDraw ω t) then (1 : ℝ) else 0)
      ∂parentDrawLaw R O M K count) =
      (groupSharedDrawLaw (M := M) count).real {draw | failure draw = true} := by
  rw [parentDrawLaw_group_mean R O M K count t (fun draw => if failure draw then (1 : ℝ) else 0),
    bool_indicator_integral]

/-- Integrating the deterministic first-crossing transfer needs only the
exact online marginals and per-time group probabilities. -/
theorem parentDrawLaw_firstCrossing_bound (R O M K : ℕ) [NeZero R] [NeZero M] [NeZero O]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (count : Fin K → ℕ) (S C : ℕ)
    (regret : ParentRandomSpace R O M K count → ℕ → ℝ)
    (prefixPayoff : ℕ → Fin O → ℝ) (failure : ℕ → ParentGroupDraw M K count → Bool)
    (budget crossingCharge failureCharge q : ℝ) (hcharge : 0 ≤ failureCharge)
    (hpoint : ∀ ω, (∑ t ∈ range S, regret ω t) ≤
      (∑ t ∈ range C, prefixPayoff t (parentOnlineDraw ω t)) + crossingCharge +
        failureCharge * ∑ t ∈ range S, (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0))
    (hprefix : (∑ t ∈ range C, uniformMean (prefixPayoff t)) ≤ budget)
    (hfailure : ∀ t < S, (groupSharedDrawLaw (M := M) count).real {draw | failure t draw = true} ≤ q) :
    (∫ ω, (∑ t ∈ range S, regret ω t) ∂parentDrawLaw R O M K count) ≤
      budget + crossingCharge + failureCharge * S * q := by
  let μ := parentDrawLaw R O M K count
  have hmean := integral_mono (μ := μ) (.of_finite) (.of_finite) hpoint
  have hprefixMean : (∫ ω, (∑ t ∈ range C, prefixPayoff t (parentOnlineDraw ω t)) ∂μ) =
      ∑ t ∈ range C, uniformMean (prefixPayoff t) := by
    rw [integral_finsetSum _ (by intro t ht; exact .of_finite)]
    exact sum_congr rfl fun t _ => parentDrawLaw_online_mean R O M K count t (prefixPayoff t)
  have hfailureMean : (∫ ω, (∑ t ∈ range S,
      (if failure t (parentGroupDraw ω t) then (1 : ℝ) else 0)) ∂μ) ≤ (S : ℝ) * q := by
    rw [integral_finsetSum _ (by intro t ht; exact .of_finite)]
    have hsum := sum_le_sum (s := range S) fun t ht =>
      (parentDrawLaw_group_failure_mean R O M K count t (failure t)).trans_le (hfailure t (mem_range.mp ht))
    simpa only [sum_const, card_range, nsmul_eq_mul] using hsum
  rw [integral_add (.of_finite) (.of_finite), integral_add (.of_finite) (integrable_const _),
    integral_const, probReal_univ, one_smul, integral_const_mul, hprefixMean] at hmean
  have hfailureCost := mul_le_mul_of_nonneg_left hfailureMean hcharge
  nlinarith only [hmean, hprefix, hfailureCost]

end EditApproximation

end OAI
