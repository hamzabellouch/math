import Mathlib
import OAI.Analysis.FreeWords.MatrixConditionalExpectation
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer KKMatrixExpectation

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev MatrixAlgebra (n : ℕ) (M : VonNeumannAlgebra H) :=
  Matrix (Fin n) (Fin n) (ConcreteAlgebra M)

def matrixTrace {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) (n : ℕ)
    (x : MatrixAlgebra n M) : ℂ := (n : ℂ)⁻¹ * ∑ i, τ.map (x i i)

def FiniteAmplifiedNumericalModel : Prop :=
  ∀ (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
  ∀ n : ℕ, 0<n → ∀ (K : Finset ℤ) (F : Finset (List (ℤ × Matrix (Fin n) (Fin n) ℂ))),
    (∀ w∈F, w≠[]) → (∀ w∈F, ∀ z∈w, z.1≠0 ∧ Matrix.trace z.2=0) →
  ∀ ε : ℝ, 0<ε → ∃ d : ℕ, 0<d ∧
    ∃ ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
    Function.Injective ρ ∧ ∃ U : unitary (MatrixAlgebra n M),
      (∀i j,U.val i j∈ρ.range) ∧
      (∀k∈K,k≠0 → ‖matrixTrace τ n ((U^k).val)‖<ε) ∧
      (∀w∈F,‖matrixTrace τ n
        ((w.map (fun z => (U^z.1).val*numericalHom (A := ConcreteAlgebra M) n z.2)).prod)‖<ε)

end

end KKFreeLiftFrontier
end

end OAI
