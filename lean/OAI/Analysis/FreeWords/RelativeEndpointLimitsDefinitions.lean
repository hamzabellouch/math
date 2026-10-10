import Mathlib
import OAI.Analysis.FreeWords.ControlledMatrixConjugation
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKRelativeEndpoints

noncomputable section

open Filter KKHaarEndpoints KKControlledConjugation KKRelativeMatrix

open scoped Topology

variable {A:Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def relativePair {n:ℕ} (u:unitary A)
    (w:List (Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A)) :=
  (w.map fun z => amplifyConj n u z.1*z.2).prod

def RelativeEndpointLimits : Prop :=
  ∀ (ι:Type*) (L:Filter ι) (τ:A →ₗ[ℂ] ℂ) (u:ι → unitary A),
  τ 1=1 → (∀a b,τ (a*b)=τ (b*a)) →
  (∀k:ℤ,k≠0 → Tendsto (fun j => τ (u j^k).val) L (𝓝 0)) →
  (∀w:List (ℤ×A),w≠[] → CenteredPowerWord τ ⊤ w →
    Tendsto (fun j => τ (powerWord (u j) w)) L (𝓝 0)) →
  ∀n:ℕ,∀w:List (Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A),
    (∀z∈w,∀a b,τ (z.1 a b)=0 ∧ τ (z.2 a b)=0) →
    (w≠[] → ∀a b,Tendsto (fun j => τ (relativePair (u j) w a b)) L (𝓝 0)) ∧
    (∀c:Matrix (Fin n) (Fin n) A,(∀a b,τ (c a b)=0) → ∀a b,
      Tendsto (fun j => τ ((relativePair (u j) w*amplifyConj n (u j) c) a b)) L (𝓝 0))

end

end KKRelativeEndpoints
end

end OAI
