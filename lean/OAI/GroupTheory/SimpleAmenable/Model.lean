import Mathlib

namespace OAI

open scoped symmDiff

namespace SimpleAmenable

noncomputable def FolnerAmenable (G : Type*) [Group G] : Prop := by
  classical
  exact ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
    ∃ D : Finset G, D.Nonempty ∧ ∀ g ∈ K,
      (((D.image (fun d => g * d)) ∆ D).card : ℝ) < ε * D.card

def MainStatement : Prop := ∃ (G : Type) (_ : Group G),
    Infinite G ∧ Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧ FolnerAmenable G

end SimpleAmenable

end OAI
