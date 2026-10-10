import Mathlib
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FiniteNumericalModel : Prop :=
  ∀ (M : VonNeumannAlgebra H), FaithfulNormalTrace M → IsFactor M → IsDiffuse M →
  ∀ n : ℕ, 0<n → ∀ (K : Finset ℤ) (F : Finset (List (ℤ × Matrix (Fin n) (Fin n) ℂ))),
    (∀ w∈F, w≠[]) → (∀ w∈F, ∀ z∈w, z.1≠0 ∧ Matrix.trace z.2=0) →
  ∀ ε : ℝ, 0<ε → ∃ d : ℕ, 0<d ∧
    ∃ U : unitary (Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ),
      (∀ k∈K, k≠0 → ‖((n*d:ℕ):ℂ)⁻¹*Matrix.trace ((U^k).val)‖<ε) ∧
      (∀ w∈F, ‖((n*d:ℕ):ℂ)⁻¹*Matrix.trace
        ((w.map (fun z => (U^z.1).val*Matrix.kronecker z.2 (1 : Matrix (Fin d) (Fin d) ℂ))).prod)‖<ε)

end

end KKVariableUltra
end

end OAI
