import Mathlib.LinearAlgebra.Prod

namespace OAI

namespace ArExplicit

section Fiber

variable {k : Type*} [Ring k]
variable {B₀ B₁ B₂ C₀ C₁ C₂ : Type*}
variable [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
variable [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
variable [Module k B₀] [Module k B₁] [Module k B₂]
variable [Module k C₀] [Module k C₁] [Module k C₂]

theorem fiber_cocycle_is_boundary
    (dB₀ : B₀ →ₗ[k] B₁) (dB₁ : B₁ →ₗ[k] B₂)
    (dC₀ : C₀ →ₗ[k] C₁) (dC₁ : C₁ →ₗ[k] C₂)
    (f₀ : B₀ →ₗ[k] C₁) (f₁ : B₁ →ₗ[k] C₂)
    (hf : ∀ a, f₁ (dB₀ a) = dC₁ (f₀ a))
    (hinj : ∀ b, dB₁ b = 0 → (∃ c, f₁ b = dC₁ c) → ∃ a, dB₀ a = b)
    (hsurj : ∀ c, dC₁ c = 0 → ∃ a, dB₀ a = 0 ∧ ∃ e, f₀ a - dC₀ e = c)
    (b : B₁) (c : C₁) (hb : dB₁ b = 0) (hc : f₁ b = dC₁ c) :
    ∃ a : B₀, ∃ e : C₀, dB₀ a = b ∧ f₀ a - dC₀ e = c := by
  obtain ⟨a, ha⟩ := hinj b hb ⟨c, hc⟩
  have hcycle : dC₁ (c - f₀ a) = 0 := by
    rw [map_sub, ← hf, ha, hc, sub_self]
  obtain ⟨u, hu, e, he⟩ := hsurj (c - f₀ a) hcycle
  refine ⟨a + u, e, ?_, ?_⟩
  · rw [map_add, ha, hu, add_zero]
  · rw [map_add, add_sub_assoc, he, add_sub_cancel]

theorem fiber_nonboundary_of_projection
    (dB₀ : B₀ →ₗ[k] B₁) (dC₀ : C₀ →ₗ[k] C₁) (f₀ : B₀ →ₗ[k] C₁)
    (b : B₁) (c : C₁) (hb : ¬ ∃ a, dB₀ a = b) :
    ¬ ∃ a : B₀, ∃ e : C₀, dB₀ a = b ∧ f₀ a - dC₀ e = c := by
  rintro ⟨a, e, ha, he⟩
  exact hb ⟨a, ha⟩

end Fiber
end ArExplicit

end OAI
