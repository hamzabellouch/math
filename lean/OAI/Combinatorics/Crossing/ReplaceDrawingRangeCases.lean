import OAI.Combinatorics.Crossing.ReplaceDrawingEdges

namespace OAI

noncomputable section
namespace Zarankiewicz.ContinuousDrawing
variable {m n : ℕ}

theorem replaceTwoRoutes_range_cases (D : ContinuousDrawing m n) (e f : BipartiteEdge m n)
    (γ : Path (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (δ : Path (D.vertex (.inl f.1)) (D.vertex (.inr f.2)))
    (g : BipartiteEdge m n) (x : Plane) (hx : x ∈ Set.range (D.replaceTwoRoutes e f γ δ g)) :
    (g=e ∧ x ∈ Set.range γ) ∨ (g=f ∧ x ∈ Set.range δ) ∨
      (g ≠ e ∧ g ≠ f ∧ x ∈ Set.range (D.edge g)) := by
  classical
  by_cases hge : g=e
  · subst g
    exact Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_first] using hx⟩
  by_cases hgf : g=f
  · subst g
    exact Or.inr (Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_second D e f (Ne.symm hge)] using hx⟩)
  · exact Or.inr (Or.inr ⟨hge,hgf,by simpa only [replaceTwoRoutes_other D e f γ δ g hge hgf] using hx⟩)

end Zarankiewicz.ContinuousDrawing

end

end OAI
