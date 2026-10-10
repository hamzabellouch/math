import Mathlib
import OAI.Analysis.FreeWords.BoundedStrongContinuity
import OAI.Analysis.FreeWords.CenteredMatrixDensityDefinitions
import OAI.Analysis.FreeWords.TraceStrongContinuity

namespace OAI

noncomputable section

namespace KKTraceTransfer

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centered_matrix_countable_dense [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (n : ℕ) :
    ∃ a : ℕ → Matrix (Fin n) (Fin n) (ConcreteAlgebra M),
      (∀ j, amplifiedTrace M τ n (a j) = 0) ∧
      (∀ j i k, ‖a j i k‖ ≤ 1) ∧
      ∀ x : Matrix (Fin n) (Fin n) (ConcreteAlgebra M),
        amplifiedTrace M τ n x = 0 → (∀ i k, ‖x i k‖ ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ∃ j, ∀ i k, traceNorm τ (a j i k - x i k) < ε := by
  classical
  obtain ⟨D,hD⟩ := TopologicalSpace.exists_dense_seq H
  let B := {x : Matrix (Fin n) (Fin n) (ConcreteAlgebra M) //
    amplifiedTrace M τ n x = 0 ∧ ∀ i k, ‖x i k‖ ≤ 1}
  let : Inhabited B := ⟨⟨0,by simp [amplifiedTrace]⟩⟩
  let E : B → ((Fin n × Fin n) × ℕ → H) :=
    fun a p => (a.val p.1.1 p.1.2 : H →L[ℂ] H) (D p.2)
  let : TopologicalSpace B := TopologicalSpace.induced E inferInstance
  have hE : Topology.IsInducing E := ⟨rfl⟩
  let : SecondCountableTopology B := hE.secondCountableTopology
  have hec : Continuous E := continuous_induced_dom
  have hc (i k : Fin n) (ξ : H) :
      Continuous (fun a : B => (a.val i k : H →L[ℂ] H) ξ) := by
    apply bounded_evals_continuous (fun a : B => (a.val i k : H →L[ℂ] H))
      (fun a => a.property.2 i k) D hD
    intro j
    exact (continuous_apply ((i,k),j)).comp hec
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq B
  refine ⟨fun j => (a j).val,fun j => (a j).property.1,fun j => (a j).property.2,?_⟩
  intro x hx hb ε hε
  have ht (i k : Fin n) :
      Continuous (fun b : B => traceNorm τ (b.val i k - x i k)) :=
    traceNorm_strong_continuous M τ (fun b : B => b.val i k)
      (fun b => b.property.2 i k) (hc i k) (x i k) (hb i k)
  let O := {b : B | ∀ i k, traceNorm τ (b.val i k - x i k) < ε}
  have ho : IsOpen O := by
    dsimp only [O]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_Iio.preimage (ht i k)
  have hn : O.Nonempty := by
    refine ⟨⟨x,hx,hb⟩,?_⟩
    intro i k
    change traceNorm τ (x i k-x i k) < ε
    simpa [traceNorm] using hε
  obtain ⟨b,hb',j,hj⟩ := ha.inter_open_nonempty O ho hn
  refine ⟨j,?_⟩
  change (a j) ∈ O
  rw [hj]
  exact hb'

end

end KKTraceTransfer
end

end OAI
