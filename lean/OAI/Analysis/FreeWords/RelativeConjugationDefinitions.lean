import Mathlib
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKRelativeMatrix

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarConjugate {M : VonNeumannAlgebra H} {n : ℕ}
    (u : unitary (ConcreteAlgebra M)) (X : Matrix (Fin n) (Fin n) (ConcreteAlgebra M)) : Matrix (Fin n) (Fin n) (ConcreteAlgebra M) :=
  Matrix.diagonal (fun _ : Fin n => u.val)*X*
    Matrix.diagonal (fun _ : Fin n => (u⁻¹).val)

def FiniteRelativeConjugation : Prop :=
  ∀ (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
  ∀ (n : ℕ) (K : Finset ℤ) (F : Finset (List (Matrix (Fin n) (Fin n) (ConcreteAlgebra M) × Matrix (Fin n) (Fin n) (ConcreteAlgebra M)))),
    (∀ w∈F, w≠[]) →
    (∀ w∈F, ∀ z∈w, ∀ i j, τ.map (z.1 i j)=0 ∧ τ.map (z.2 i j)=0) →
  ∀ ε : ℝ, 0<ε → ∃ u : unitary (ConcreteAlgebra M),
    (∀ k∈K, k≠0 → ‖τ.map ((u^k).val)‖<ε) ∧
    (∀ w∈F, ∀ i j,
      ‖τ.map (((w.map (fun (z : Matrix (Fin n) (Fin n) (ConcreteAlgebra M) × Matrix (Fin n) (Fin n) (ConcreteAlgebra M)) => scalarConjugate u z.1*z.2)).prod) i j)‖<ε)

end

end KKRelativeMatrix
end

end OAI
