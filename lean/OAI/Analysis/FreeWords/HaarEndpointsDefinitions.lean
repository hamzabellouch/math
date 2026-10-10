import Mathlib

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

def powerWord (u : unitary A) (w : List (ℤ×A)) : A :=
  (w.map fun z => (u^z.1).val*z.2).prod

def CenteredPowerWord (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) (w : List (ℤ×A)) : Prop :=
  ∀z∈w,z.1≠0 ∧ z.2∈B ∧ τ z.2=0

def HaarEndpointCompletion : Prop :=
  ∀ (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) (u : unitary A),
  τ 1=1 → (∀a b,τ (a*b)=τ (b*a)) →
  (∀k:ℤ,k≠0 → τ (u^k).val=0) →
  (∀w:List (ℤ×A),w≠[] → CenteredPowerWord τ B w → τ (powerWord u w)=0) →
  ∀w:List (ℤ×A),CenteredPowerWord τ B w → ∀k:ℤ,k≠0 →
    τ (powerWord u w*(u^k).val)=0

end

end KKHaarEndpoints
end

end OAI
