import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions
import OAI.Analysis.FreeWords.MatrixConditionalExpectation

namespace OAI

noncomputable section

namespace KKMatrixExpectation

noncomputable section

open Filter KKHaarEndpoints

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def MatrixPowerBlockLimits : Prop :=
  ∀(ι:Type*) (L:Filter ι) (τ:A →ₗ[ℂ] ℂ),τ 1=1 →
    (∀a b,τ (a*b)=τ (b*a)) → ∀n:ℕ,0<n →
    ∀u:ι → unitary (Matrix (Fin n) (Fin n) A),
    (∀k:ℤ,k≠0 → Tendsto (fun j => matrixTraceMap τ n (u j^k).val) L (𝓝 0)) →
    (∀w:List (ℤ×Matrix (Fin n) (Fin n) A),w≠[] →
      CenteredPowerWord (matrixTraceMap τ n) (numericalHom n).range.toSubalgebra w →
      Tendsto (fun j => matrixTraceMap τ n (powerWord (u j) w)) L (𝓝 0)) →
    ∀w:List (ℤ×Matrix (Fin n) (Fin n) A),
      CenteredPowerWord (matrixTraceMap τ n) (numericalHom n).range.toSubalgebra w →
      ∀k:ℤ,k≠0 → ∀a b:Fin n,
      Tendsto (fun j => τ ((powerWord (u j) w*(u j^k).val) a b)) L (𝓝 0)

end

end KKMatrixExpectation
end

end OAI
