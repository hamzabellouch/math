import Mathlib
import OAI.Analysis.FreeWords.BoundedStrongContinuity
import OAI.Analysis.FreeWords.TraceStrongContinuity

namespace OAI

noncomputable section

namespace KKTraceTransfer

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem trace_unit_ball_countable_dense [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) :
    ∃ a : ℕ → ConcreteAlgebra M, (∀ j, ‖a j‖ ≤ 1) ∧
      ∀ x : ConcreteAlgebra M, ‖x‖ ≤ 1 → ∀ ε : ℝ, 0 < ε →
        ∃ j, traceNorm τ (a j - x) < ε := by
  classical
  obtain ⟨D,hD⟩ := TopologicalSpace.exists_dense_seq H
  let B := {x : ConcreteAlgebra M // ‖x‖ ≤ 1}
  let : Inhabited B := ⟨⟨0,by simp⟩⟩
  let E : B → (ℕ → H) := fun a j => (a.val : H →L[ℂ] H) (D j)
  let : TopologicalSpace B := TopologicalSpace.induced E inferInstance
  have hE : Topology.IsInducing E := ⟨rfl⟩
  let : SecondCountableTopology B := hE.secondCountableTopology
  have hec : Continuous E := continuous_induced_dom
  have hc (ξ : H) : Continuous (fun a : B => (a.val : H →L[ℂ] H) ξ) := by
    apply bounded_evals_continuous (fun a : B => (a.val : H →L[ℂ] H))
      (fun a => a.property) D hD
    intro j
    exact (continuous_apply j).comp hec
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq B
  refine ⟨fun j => (a j).val,fun j => (a j).property,?_⟩
  intro x hx ε hε
  have ht : Continuous (fun b : B => traceNorm τ (b.val-x)) :=
    traceNorm_strong_continuous M τ (fun b : B => b.val) (fun b => b.property) hc x hx
  have ho : IsOpen {b : B | traceNorm τ (b.val-x) < ε} := isOpen_Iio.preimage ht
  have hn : ({b : B | traceNorm τ (b.val-x) < ε} : Set B).Nonempty := by
    refine ⟨⟨x,hx⟩,?_⟩
    change traceNorm τ (x-x) < ε
    simpa [traceNorm] using hε
  obtain ⟨b,hb,j,hj⟩ := ha.inter_open_nonempty _ ho hn
  refine ⟨j,?_⟩
  change traceNorm τ ((a j).val-x) < ε
  rw [hj]
  exact hb

end

end KKTraceTransfer
end

end OAI
