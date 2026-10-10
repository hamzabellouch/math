import Mathlib
import OAI.Analysis.FreeWords.AmplifiedModelDefinitions

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def mixedMoment {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) {n : ℕ}
    (U : unitary (MatrixAlgebra n M)) (w : List (ℤ × MatrixAlgebra n M)) : ℂ :=
  matrixTrace τ n ((w.map fun z => (U ^ z.1).val * z.2).prod)

def IsCenteredTest {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) {n : ℕ}
    (w : List (ℤ × MatrixAlgebra n M)) : Prop :=
  w ≠ [] ∧ ∀ z ∈ w, z.1 ≠ 0 ∧ matrixTrace τ n z.2 = 0

def FiniteMatrixFreeApproximation : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [Nontrivial H] (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
    ∀ n : ℕ, 0 < n → ∀ (F : Finset (List (ℤ × MatrixAlgebra n M))),
    (∀ w ∈ F, IsCenteredTest τ w) → ∀ K : Finset ℤ, ∀ ε : ℝ, 0 < ε →
    ∃ d : ℕ, 0 < d ∧ ∃ ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      Function.Injective ρ ∧ ∃ U : unitary (MatrixAlgebra n M),
        (∀ i j, U.val i j ∈ ρ.range) ∧
        (∀ k ∈ K, k ≠ 0 → ‖matrixTrace τ n (U ^ k).val‖ < ε) ∧ (∀ w ∈ F, ‖mixedMoment τ U w‖ < ε)

end

end KKFreeLiftFrontier
end

end OAI
