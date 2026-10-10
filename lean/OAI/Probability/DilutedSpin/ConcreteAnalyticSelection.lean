import OAI.Probability.DilutedSpin.VertexContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot Filter Set
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

/-- Selection and analytic extraction for the literal physical diluted model.
There is one parameter vector per selected size and ONE complete old reservoir
for all trees, tests, colors, and probe indices. No score or coefficient-limit
assumption occurs in this statement. This is the bounded-stage producer,
not the main variational formula. -/
theorem actual_analytic_selection (M : Model p) {C H c : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (hm : ∀ l, c ≤ m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    (hw : ∀ j, 0 < ν.real {j})
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → K×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, increment ν Q m D E M (Ns n) (us n) ≤ liminf (pressure M) atTop+ε) ∧
      (∀ j, Tendsto (fun n => scoreError ν Q m D E M C H j (Ns n+1) (us n)) atTop (𝓝 0)) ∧
      (∀ (S : PrescribedTree (L+1)) (anchor : S.Leaf)
        (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
        (B : ℝ), 0 ≤ B → (∀ n x, |f n x| ≤ B) → ∀ q k,
        Tendsto (fun n => physicalCoefficient ν Q m D E S anchor M C H (Ns n+1) (us n) (f n) q k)
          atTop (𝓝 0)) := by
  obtain ⟨Ns,us,hNs,hu,hi,he⟩ := actual_parameter_selection ν Q m D E M hC hH hc
    hθ hh hθi hhi hm hend hw hD hE hε
  refine ⟨Ns,us,hNs,hu,hi,he,?_⟩
  intro S anchor f B hB hf q k
  exact physical_coefficients_tendsto ν Q m D E S anchor M C H Ns us f
    (fun l => hc.trans_le (hm l)) hmono hend hB hf hD hE hw he q k

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
