import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedCoordinateProducts

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y : C} (n : ℤ) (e : X ≅ Y⟦n⟧)

theorem negativeShiftIso_comp_hom :
    ShiftedHom.comp (negativeShiftIso n e).hom e.hom (by omega : n + -n = 0) =
      ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 Y) := by
  simp only [negativeShiftIso, ShiftedHom.comp, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp [shiftFunctorCompIsoId, ShiftedHom.mk₀, shiftFunctorZero']

theorem hom_comp_negativeShiftIso :
    ShiftedHom.comp e.hom (negativeShiftIso n e).hom (by omega : -n+n=0) =
      ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 X) := by
  apply (cancel_mono ((CategoryTheory.shiftFunctor C (0:ℤ)).map e.hom ≫
    (shiftFunctorAdd' C n 0 n (add_zero n)).inv.app Y)).mp
  change ShiftedHom.comp (ShiftedHom.comp e.hom (negativeShiftIso n e).hom _) e.hom _ =
    ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 X)) e.hom _
  rw [ShiftedHom.comp_assoc e.hom (negativeShiftIso n e).hom e.hom
    (by omega : -n+n=0) (by omega : n + -n=0) (by omega : n + -n+n=n), negativeShiftIso_comp_hom,
    ShiftedHom.comp_mk₀_id, ShiftedHom.mk₀_id_comp]

end ArExplicit

end

end OAI
