import OAI.Algebra.AuslanderReiten.Resolutions.CoverFullHomAction

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
section Category
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n : ℤ) (e : X ≅ Y⟦n⟧)
variable (s : Y ≅ Z⟦(1 : ℤ)⟧) (t : X ≅ Z⟦n+1⟧)
variable (ht : t.hom = ShiftedHom.comp e.hom s.hom (add_comm 1 n))

include ht in
theorem negativeShiftIso_step :
    ShiftedHom.comp s.hom (negativeShiftIso (n+1) t).hom
      (by omega : -(n+1)+1 = -n) = (negativeShiftIso n e).hom := by
  apply (CategoryTheory.shiftFunctor C n).map_injective
  apply (cancel_epi e.hom).mp
  apply (cancel_mono ((shiftFunctorAdd' C (-n) n 0 (by omega)).inv.app X)).mp
  simp only [Category.assoc]
  change ShiftedHom.comp e.hom
    (ShiftedHom.comp s.hom (negativeShiftIso (n+1) t).hom (by omega : -(n+1)+1 = -n))
      (by omega : -n+n=0) =
      ShiftedHom.comp e.hom (negativeShiftIso n e).hom (by omega : -n+n=0)
  rw [← ShiftedHom.comp_assoc e.hom s.hom (negativeShiftIso (n+1) t).hom
    (add_comm 1 n) (by omega : -(n+1)+1 = -n) (by omega), ← ht,
    hom_comp_negativeShiftIso, hom_comp_negativeShiftIso]

include ht in
theorem shiftedNegative_step (a : ℤ) (v : S ⟶ Y⟦a⟧) :
    ShiftedHom.comp (ShiftedHom.comp v s.hom (add_comm 1 a))
      (negativeShiftIso (n+1) t).hom (by omega : -(n+1)+(a+1)=a-n) =
    ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=a-n) := by
  rw [ShiftedHom.comp_assoc v s.hom (negativeShiftIso (n+1) t).hom
    (add_comm 1 a) (by omega : -(n+1)+1 = -n) (by omega),
    negativeShiftIso_step n e s t ht]

end Category
end ArExplicit

end

end OAI
