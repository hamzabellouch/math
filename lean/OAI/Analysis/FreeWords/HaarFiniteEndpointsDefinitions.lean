import Mathlib
import OAI.Analysis.FreeWords.HaarEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKHaarEndpoints

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

def FiniteCyclicApprox (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) (Good : unitary A → Prop) : Prop :=
  ∀ (K : Finset ℤ) (F : Finset (List (ℤ×A))),
    (∀w∈F,w≠[] ∧ CenteredPowerWord τ B w) → ∀ε:ℝ,0<ε →
    ∃u:unitary A, Good u ∧
      (∀k∈K,k≠0 → ‖τ (u^k).val‖<ε) ∧ (∀w∈F,‖τ (powerWord u w)‖<ε)

def HaarFiniteEndpoints : Prop :=
  ∀ (τ : A →ₗ[ℂ] ℂ) (B : Subalgebra ℂ A) (Good : unitary A → Prop),
    τ 1=1 → (∀a b,τ (a*b)=τ (b*a)) → FiniteCyclicApprox τ B Good →
    ∀ (K : Finset ℤ) (F : Finset (List (ℤ×A)))
      (E : Finset (List (ℤ×A) × ℤ)),
      (∀w∈F,w≠[] ∧ CenteredPowerWord τ B w) →
      (∀z∈E,CenteredPowerWord τ B z.1 ∧ z.2≠0) → ∀ε:ℝ,0<ε →
      ∃u:unitary A, Good u ∧
        (∀k∈K,k≠0 → ‖τ (u^k).val‖<ε) ∧
        (∀w∈F,‖τ (powerWord u w)‖<ε) ∧
        (∀z∈E,‖τ (powerWord u z.1*(u^z.2).val)‖<ε)

end

end KKHaarEndpoints
end

end OAI
