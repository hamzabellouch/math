import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions
import OAI.Analysis.FreeWords.MatrixConditionalExpectation

namespace OAI

noncomputable section

namespace KKMatrixBounds

noncomputable section

open KKHaarEndpoints KKMatrixExpectation Filter

open scoped Matrix.Norms.Operator Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def wordBound (n:ℕ) (w:List (ℤ×Matrix (Fin n) (Fin n) A)) : ℝ :=
  (w.map fun z => (n:ℝ)*‖z.2‖).prod

def AmplifiedBlockBounds : Prop :=
  (∀n:ℕ,∀U:unitary (Matrix (Fin n) (Fin n) A),∀w:List (ℤ×Matrix (Fin n) (Fin n) A),
    ‖powerWord U w‖≤wordBound n w) ∧
  (∀(ι:Type) (L:Filter ι) (τ:A →ₗ[ℂ] ℂ) (n:ℕ)
    (X:ι → Matrix (Fin n) (Fin n) A),
    (∀a b,Tendsto (fun j => τ (X j a b)) L (𝓝 0)) →
    Tendsto (fun j => matrixExpectation τ n (X j)) L (𝓝 0))

end

end KKMatrixBounds
end

end OAI
