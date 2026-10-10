import OAI.Algebra.Finitistic.Selected.SelectedRectification

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedWindow
open SelectedFixedDiagram SelectedRectification

/-- A common finite support window chosen from the fixed representatives alone. -/
structure Window where
  lo : ℤ
  hi : ℤ
  bound0 : ∀ n, n < lo ∨ hi < n → IsZero (D0.X n)
  bound1 : ∀ n, n < lo ∨ hi < n → IsZero (D1.X n)
  bound2 : ∀ n, n < lo ∨ hi < n → IsZero (D2.X n)

instance : Nonempty Window := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded P fixed.D0
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded P fixed.D1
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded P fixed.D2
  refine ⟨⟨min l₀ (min l₁ l₂), max h₀ (max h₁ h₂), ?_, ?_, ?_⟩⟩
  · intro n hn; apply b₀ n; omega
  · intro n hn; apply b₁ n; omega
  · intro n hn; apply b₂ n; omega

def window : Window := Classical.choice inferInstance
abbrev lo := window.lo
abbrev hi := window.hi

/-- Every term outside the fixed total's resulting support window is zero. -/
theorem bounded (n : ℤ) (hn : n < lo - 2 ∨ hi < n) : IsZero (bimodule.X n) :=
  InducedRectification.total_bounded (ConcreteQuadraticDiagram.quadratic P)
    D0 D1 D2 f g relations lo hi window.bound0 window.bound1 window.bound2 n hn

/-- The support choices retain the complete proved rectification certificate. -/
theorem verified : RectificationLemma.Verified P D0 D1 D2 f g relations lo hi :=
  RectificationLemma.rectification P D0 D1 D2 f g relations lo hi
    window.bound0 window.bound1 window.bound2
    (UnderlyingRepresentatives.projective P fixed.D0)
    (UnderlyingRepresentatives.projective P fixed.D1)
    (UnderlyingRepresentatives.projective P fixed.D2)
    (UnderlyingRepresentatives.finite P fixed.D0)
    (UnderlyingRepresentatives.finite P fixed.D1)
    (UnderlyingRepresentatives.finite P fixed.D2)
end LittleFinitistic.SelectedWindow

end

end OAI
