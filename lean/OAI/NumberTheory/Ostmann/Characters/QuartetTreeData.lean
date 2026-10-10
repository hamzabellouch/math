import OAI.NumberTheory.Ostmann.Tree.RationalQuartetValue

namespace OAI

/-! # Every depth-two tree has the concrete quartet data used by the local bounds -/

namespace Ostmann

theorem RationalTreeData.exists_pair {U : Type*} [CommGroup U] {C : U}
    (T : RationalTreeData U 1 C) :
    ∃ s C₁ C₂ u s₁ s₂ : U, ∃ h : C₁ * C₂ = C,
      h ▸ RationalTreeData.node s C₁ C₂ u
        (.leaf s₁ (u * C₁)) (.leaf s₂ (u * C₂)) = T := by
  cases T with
  | node s C₁ C₂ u left right =>
    cases left with
    | leaf s₁ _ =>
      cases right with
      | leaf s₂ _ => exact ⟨s, C₁, C₂, u, s₁, s₂, rfl, rfl⟩

theorem RationalTreeData.exists_quartet {U : Type*} [CommGroup U] {C : U}
    (T : RationalTreeData U 2 C) :
    ∃ Q : RationalQuartetData U, ∃ h : Q.CL * Q.CR = C, h ▸ Q.tree = T := by
  cases T with
  | node s CL CR u left right =>
    obtain ⟨sL, C₁, C₂, uL, s₁, s₂, hL, eL⟩ := left.exists_pair
    obtain ⟨sR, C₃, C₄, uR, s₃, s₄, hR, eR⟩ := right.exists_pair
    rw [← eL, ← eR]
    exact ⟨⟨s, sL, sR, u, CL, CR, s₁, s₂, s₃, s₄, uL, uR,
      C₁, C₂, C₃, C₄, hL, hR⟩, rfl, rfl⟩

end Ostmann

end OAI
