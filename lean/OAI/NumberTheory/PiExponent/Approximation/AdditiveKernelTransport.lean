import Mathlib

namespace OAI

namespace PiExponent.AdditiveKernelTransport

variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']

theorem equiv_zero (e : A ≃+ B) : e 0 = 0 := map_zero e

def kernelEquiv (e : A ≃+ B) (e' : A' ≃+ B')
    (d : A →+ A') (D : B →+ B') (h : ∀ x, e' (d x) = D (e x)) :
    d.ker ≃+ D.ker where
  toFun c := ⟨e c.val, by
    change D (e c.val) = 0
    rw [← h, c.property, map_zero]⟩
  invFun c := ⟨e.symm c.val, by
    change d (e.symm c.val) = 0
    apply e'.injective
    rw [h, e.apply_symm_apply, map_zero]
    exact c.property⟩
  left_inv c := Subtype.ext (e.symm_apply_apply c.val)
  right_inv c := Subtype.ext (e.apply_symm_apply c.val)
  map_add' c b := Subtype.ext (map_add e c.val b.val)

theorem kernelEquiv_val (e : A ≃+ B) (e' : A' ≃+ B')
    (d : A →+ A') (D : B →+ B') (h : ∀ x, e' (d x) = D (e x))
    (c : d.ker) : (kernelEquiv e e' d D h c).val = e c.val := rfl

theorem transport_primitives {A₂ B₂ : Type*} [AddCommGroup A₂] [AddCommGroup B₂]
    (e₀ : A ≃+ B) (e₁ : A' ≃+ B') (e₂ : A₂ ≃+ B₂)
    (d₀ : A →+ A') (d₁ : A' →+ A₂) (D₀ : B →+ B') (D₁ : B' →+ B₂)
    (h₀ : ∀ x, e₁ (d₀ x) = D₀ (e₀ x))
    (h₁ : ∀ x, e₂ (d₁ x) = D₁ (e₁ x))
    (hp : ∀ c, D₁ c = 0 → ∃ b, D₀ b = c) :
    ∀ c, d₁ c = 0 → ∃ b, d₀ b = c := by
  intro c hc
  have hclosed : D₁ (e₁ c) = 0 := by rw [← h₁, hc, map_zero]
  obtain ⟨b, hb⟩ := hp (e₁ c) hclosed
  refine ⟨e₀.symm b, e₁.injective ?_⟩
  rw [h₀, e₀.apply_symm_apply, hb]

end PiExponent.AdditiveKernelTransport

end OAI
