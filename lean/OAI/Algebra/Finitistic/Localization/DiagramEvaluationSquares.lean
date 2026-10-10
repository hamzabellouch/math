import Mathlib.CategoryTheory.Functor.Category

namespace OAI
open CategoryTheory
namespace LittleFinitistic.DiagramEvaluationSquares
universe u v
variable {C : Type u} [Category.{v} C]

/-- Compose two isomorphisms of arrow diagrams, retaining the displayed arrow. -/
theorem compose {A₀ A₁ B₀ B₁ C₀ C₁ : C}
    (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁) (h : C₀ ⟶ C₁)
    (i₀ : A₀ ≅ B₀) (i₁ : A₁ ≅ B₁) (j₀ : B₀ ≅ C₀) (j₁ : B₁ ≅ C₁)
    (hi : f ≫ i₁.hom = i₀.hom ≫ g) (hj : g ≫ j₁.hom = j₀.hom ≫ h) :
    f ≫ (i₁ ≪≫ j₁).hom = (i₀ ≪≫ j₀).hom ≫ h := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc,hi,Category.assoc,hj,← Category.assoc]
end LittleFinitistic.DiagramEvaluationSquares

end OAI
