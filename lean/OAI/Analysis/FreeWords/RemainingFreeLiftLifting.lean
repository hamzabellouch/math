import Mathlib
import OAI.Analysis.FreeWords.FiniteFreeDefinitions

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer Filter Topology

noncomputable section

def AllConstantMatrixFreeSequence : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [Nontrivial H] (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
    ∀ n : ℕ, 0 < n →
      ∃ d : ℕ → ℕ, (∀ j, 0 < d j) ∧
      ∃ ρ : ∀ j, Matrix (Fin (d j)) (Fin (d j)) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      (∀ j, Function.Injective (ρ j)) ∧ ∃ U : ℕ → unitary (MatrixAlgebra n M),
      (∀ j i k, (U j).val i k ∈ (ρ j).range) ∧
      (∀ k : ℤ, k ≠ 0 → Tendsto (fun j => matrixTrace τ n (U j ^ k).val) atTop (𝓝 0)) ∧
      (∀ w : List (ℤ × MatrixAlgebra n M), IsCenteredTest τ w →
        Tendsto (fun j => mixedMoment τ (U j) w) atTop (𝓝 0))

end

end KKFreeLiftFrontier
end

end OAI
