import Mathlib
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FiniteMatrixModel : Prop :=
  ∀ (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
  ∀ (n : ℕ), 0<n → ∀ (β : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M),
  ∀ (K : Finset ℤ) (F : Finset (List (ℤ × ConcreteAlgebra M))),
  (∀ w∈F, w≠[]) → (∀ w∈F, ∀ z∈w, z.1≠0 ∧ τ.map z.2=0 ∧ z.2∈β.range) →
  ∀ ε : ℝ, 0<ε → ∃ j : ℕ,
  ∃ ρ : Matrix (Fin (n*2^j)) (Fin (n*2^j)) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
    Function.Injective ρ ∧ β.range≤ρ.range ∧
    ∃ u : unitary (ConcreteAlgebra M), u.val∈ρ.range ∧
      (∀ k∈K, k≠0 → ‖τ.map ((u^k).val)‖<ε) ∧
      (∀ w∈F, ‖τ.map ((w.map (fun z => (u^z.1).val*z.2)).prod)‖<ε)

end

end KKVariableUltra
end

end OAI
