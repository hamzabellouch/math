import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.LabelRelabel
import OAI.GroupTheory.SimpleAmenable.Configurations.CellFunctor
import OAI.GroupTheory.SimpleAmenable.Simplicial.CellMonoidal

namespace OAI

section
open CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell

variable {a n m : ℕ}
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g, Reduced g → Reduced (f g))
variable (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)
noncomputable def relabelIso :
    functor P l ⋙ relabel f hf ≅ functor P ⟨f l.val,hf l.val l.property⟩ :=
  NatIso.ofComponents (fun U => asIso (X := (relabel f hf).obj (object P l U))
    (Y := object P ⟨f l.val,hf l.val l.property⟩ U)
    { arrow := 𝟙 _
      positional _ := rfl
      labelled _ := rfl }) (by
    intro U V g
    apply Hom.ext
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id]
    rfl)
noncomputable instance relabelIsoMonoidal : NatTrans.IsMonoidal (relabelIso f hf P l).hom where
  unit := by
    apply Hom.ext
    change (𝟙 _ ≫ (unitArrow P l).arrow) ≫ 𝟙 _ = (unitArrow P ⟨f l.val,hf l.val l.property⟩).arrow
    simp only [Category.id_comp,Category.comp_id]
    rfl
  tensor U V := by
    apply Hom.ext
    change (𝟙 _ ≫ (tensorArrow P l U V).arrow) ≫ 𝟙 _ =
      sumArrow (𝟙 _) (𝟙 _) ≫ (tensorArrow P ⟨f l.val,hf l.val l.property⟩ U V).arrow
    simp only [Category.id_comp,Category.comp_id,sumArrow_id]
    rfl
end SimpleAmenable.PolygonObject.Labelled.Cell

end

end OAI
