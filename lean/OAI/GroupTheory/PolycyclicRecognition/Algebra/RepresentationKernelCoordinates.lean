import Mathlib.Algebra.Group.Subgroup.Ker

namespace OAI

/-! # Faithfulness checked in a surjective coordinate system -/

namespace PolycyclicRecognition

theorem injective_of_kernel_in_coordinates {G A X : Type*} [Group G] [Group A]
    (ρ : G →* A) (f : X → G) (hf : Function.Surjective f)
    (hker : ∀ x, ρ (f x) = 1 → f x = 1) : Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨x,rfl⟩ := hf g
  exact hker x hg

end PolycyclicRecognition

end OAI
