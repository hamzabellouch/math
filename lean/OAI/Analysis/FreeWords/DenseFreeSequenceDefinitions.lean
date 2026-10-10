import Mathlib
import OAI.Analysis.FreeWords.FiniteFreeDefinitions

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer Filter Topology

noncomputable section

def DenseTestMatrixFreeSequence : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [Nontrivial H] (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
    ∀ n : ℕ, 0 < n → ∃ a : ℕ → MatrixAlgebra n M,
      (∀ j, matrixTrace τ n (a j) = 0) ∧ (∀ j i k, ‖a j i k‖ ≤ 1) ∧
      (∀ x : MatrixAlgebra n M, matrixTrace τ n x = 0 → (∀ i k, ‖x i k‖ ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ∃ j, ∀ i k, traceNorm τ (a j i k-x i k) < ε) ∧
      ∃ d : ℕ → ℕ, (∀ j, 0 < d j) ∧
      ∃ ρ : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      (∀ j, Function.Injective (ρ j)) ∧ ∃ U : ℕ → unitary (MatrixAlgebra n M),
      (∀ j i k, (U j).val i k ∈ (ρ j).range) ∧
      (∀ k : ℤ, k ≠ 0 → Tendsto (fun j => matrixTrace τ n (U j ^ k).val) atTop (𝓝 0)) ∧
      (∀ w : List (ℤ × ℕ), w ≠ [] → (∀ z ∈ w, z.1 ≠ 0) →
        Tendsto (fun j => mixedMoment τ (U j) (w.map fun z => (z.1,a z.2))) atTop (𝓝 0))

end

end KKFreeLiftFrontier
end

end OAI
