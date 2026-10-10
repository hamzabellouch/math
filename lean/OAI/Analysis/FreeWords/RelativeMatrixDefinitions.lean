import Mathlib
import OAI.Analysis.FreeWords.ProjectionSmall

namespace OAI

noncomputable section

namespace KKRelativeMatrix

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FiniteRelativeMatrixIndependence : Prop :=
  ∀ (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M), IsFactor M → IsDiffuse M →
  ∀ (n : ℕ) (K : Finset ℤ) (F : Finset (List (ℤ × Matrix (Fin n) (Fin n) (ConcreteAlgebra M)))),
  (∀ w∈F, w≠[]) →
  (∀ w∈F, ∀ z∈w, z.1≠0 ∧ ∀ i j, τ.map (z.2 i j)=0) →
  ∀ ε : ℝ, 0<ε → ∃ u : unitary (ConcreteAlgebra M),
    (∀ k∈K, k≠0 → ‖τ.map ((u^k).val)‖<ε) ∧
    (∀ w∈F, ∀ i j,
      ‖τ.map (((w.map (fun (z : ℤ × Matrix (Fin n) (Fin n) (ConcreteAlgebra M)) => Matrix.diagonal (fun _ : Fin n => (u^z.1).val)*z.2)).prod) i j)‖<ε)

end

end KKRelativeMatrix
end

end OAI
