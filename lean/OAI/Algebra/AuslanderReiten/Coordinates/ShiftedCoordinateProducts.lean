import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedObjectCoordinates
import Mathlib.CategoryTheory.Shift.ShiftedHom

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y S : C} (n : ℤ) (e : X ≅ Y⟦n⟧)

theorem shiftedNegativeIso_comp (a : ℤ) (v : S ⟶ Y⟦a⟧) :
    v ≫ (shiftedNegativeIso n e a).hom =
      ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=a-n) := by
  simp only [shiftedNegativeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, ShiftedHom.comp]

variable (k : Type w) [CommRing k] [Preadditive C] [Linear k C]

theorem shiftedNegativeHomEquiv_comp (a : ℤ) (v : S ⟶ Y⟦a⟧) :
    shiftedNegativeHomEquiv n e k S a v =
      ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=a-n) := by
  simpa only [shiftedNegativeHomEquiv, Linear.homCongr_apply, Iso.refl_inv,
    Category.id_comp] using shiftedNegativeIso_comp n e a v

end ArExplicit

end

end OAI
