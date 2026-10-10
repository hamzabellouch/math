import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

open Filter

open scoped Topology

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

def HaarLeftEndpointLimits : Prop :=
  ∀ (ι : Type*) (L : Filter ι) (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A)
    (u : ι → unitary A), τ 1=1 →
    (∀ a b,τ (a*b)=τ (b*a)) →
    (∀ k : ℤ,k≠0 → Tendsto (fun j => τ ((u j^k).val)) L (𝓝 0)) →
    (∀ w : List (ℤ×A),w≠[] → CenteredPowerWord τ B w →
      Tendsto (fun j => τ (powerWord (u j) w)) L (𝓝 0)) →
    ∀ w : List (ℤ×A),w≠[] → CenteredPowerWord τ B w → ∀ a∈B,
      Tendsto (fun j => τ (a*powerWord (u j) w)) L (𝓝 0)

end

end KKHaarEndpoints
end

end OAI
