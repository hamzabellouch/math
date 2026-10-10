import Mathlib
import OAI.Analysis.FreeWords.EntryWords
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKRelativeMatrix

noncomputable section

open Filter KKHaarEndpoints

open scoped Topology

variable {A:Type*} [Ring A] [StarRing A] [Algebra ℂ A]

def MatrixLeftEndpointLimits : Prop :=
  ∀ (ι:Type*) (L:Filter ι) (τ:A →ₗ[ℂ] ℂ) (B:Subalgebra ℂ A) (u:ι → unitary A),
  τ 1=1 → (∀a b,τ (a*b)=τ (b*a)) →
  (∀k:ℤ,k≠0 → Tendsto (fun j => τ (u j^k).val) L (𝓝 0)) →
  (∀w:List (ℤ×A),w≠[] → CenteredPowerWord τ B w →
    Tendsto (fun j => τ (powerWord (u j) w)) L (𝓝 0)) →
  ∀n:ℕ,∀w:List (ℤ×Matrix (Fin n) (Fin n) A),w≠[] →
    (∀z∈w,z.1≠0 ∧ ∀a b,z.2 a b∈B ∧ τ (z.2 a b)=0) →
  ∀a:Matrix (Fin n) (Fin n) A,(∀i j,a i j∈B) → ∀i j,
    Tendsto (fun t => τ ((a*matrixWord (fun k => (u t^k).val) w) i j)) L (𝓝 0)

end

end KKRelativeMatrix
end

end OAI
