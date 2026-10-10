import Mathlib

namespace OAI

noncomputable section

namespace KKAmalgamatedTransport

noncomputable section

variable {A D : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [AddCommGroup D] [Module ℂ D]

def pairProd (w : List (A × A)) : A := (w.map fun z => z.1*z.2).prod

def Centered (τ : A →ₗ[ℂ] ℂ) (S : StarSubalgebra ℂ A) : Set A :=
  {a | a∈S ∧ τ a=0}

def RelativeCentered (E : A →ₗ[ℂ] A) (S : StarSubalgebra ℂ A) : Set A :=
  {a | a∈S ∧ E a=0}

def AlternatingMoments (f : A →ₗ[ℂ] D) (S T : Set A) : Prop :=
  ∀ w : List (A × A), (∀ z∈w, z.1∈S ∧ z.2∈T) →
    (w≠[] → f (pairProd w)=0) ∧ (∀ c∈S, f (pairProd w*c)=0)

def ScalarAmalgamatedCyclicTransport : Prop :=
  ∀ (τ : A →ₗ[ℂ] ℂ) (E : A →ₗ[ℂ] A)
    (B C P Q : StarSubalgebra ℂ A),
    τ 1=1 → B≤P → B≤Q → C≤Q →
    (∀ a, E a∈B) → (∀ b∈B, E b=b) →
    (∀ a b, b∈B → E (a*b)=E a*b) →
    (∀ a, τ (E a)=τ a) →
    (∀ b∈B, τ (b*star b)=0 → b=0) →
    AlternatingMoments τ (Centered τ C) (Centered τ B) →
    AlternatingMoments E (RelativeCentered E Q) (RelativeCentered E P) →
    ∀ w : List (A × A), w≠[] →
      (∀ z∈w, z.1∈Centered τ C ∧ z.2∈Centered τ P) →
      τ (pairProd w)=0

end

end KKAmalgamatedTransport
end

end OAI
