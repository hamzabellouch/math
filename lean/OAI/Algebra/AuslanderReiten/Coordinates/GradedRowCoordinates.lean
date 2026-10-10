import OAI.Algebra.AuslanderReiten.Homology.TriangleConnectingProduct
import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedBoundaryComponents

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w

theorem connectingRow {k : Type u} [CommRing k] [CharP k 2]
    {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
    [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (X V W : C) (a : ℤ) (v : X ⟶ T.obj₃⟦a⟧)
    (p r : T.obj₃ ⟶ V) (s : V ⟶ W⟦(1 : ℤ)⟧) (c d : W ⟶ T.obj₁)
    (h : T.mor₃ = (p ≫ s) ≫ c⟦(1 : ℤ)⟧' + (r ≫ s) ≫ d⟦(1 : ℤ)⟧') :
    TriangleGradedSequence.connecting k T X a v =
      ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) ≫ c⟦a+1⟧' +
      ShiftedHom.comp (v ≫ r⟦a⟧') s (add_comm 1 a) ≫ d⟦a+1⟧' := by
  erw [TriangleGradedSequence.connecting_eq_product, h, shiftedComp_row]

theorem additiveRowCoordinates
    {G H I J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I]
    (e : G →+ H) (d : I →+ H) (f g : J → I)
    {w w₁ w₂ : G} {x₁ x₂ m₁ m₂ : J}
    (hw : w = w₁ + w₂) (h₁ : e w₁ = d (f x₁)) (h₂ : e w₂ = d (g x₂))
    (hm₁ : m₁ = x₁) (hm₂ : m₂ = x₂) :
    e w = d (f m₁ + g m₂) := by
  rw [hw, map_add, h₁, h₂, hm₁, hm₂, map_add]

end ArExplicit

end

end OAI
