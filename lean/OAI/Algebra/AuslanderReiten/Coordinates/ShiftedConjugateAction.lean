import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedInverse

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m : ℤ) (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

def shiftedConjugate : X ⟶ X⟦m-n⟧ :=
  ShiftedHom.comp f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0 = -n)) (by omega : -n+m=m-n)

theorem shiftedConjugate_action (a : ℤ) (v : S ⟶ Z⟦a⟧) :
    ShiftedHom.comp (v ≫ c⟦a⟧') (negativeShiftIso n e).hom (by omega : -n+a=a-n) =
      ShiftedHom.comp
        (ShiftedHom.comp v (negativeShiftIso m f).hom (by omega : -m+a=a-m))
        (shiftedConjugate n m e f c) (by omega : (m-n)+(a-m)=a-n) := by
  unfold shiftedConjugate
  rw [ShiftedHom.comp_assoc v (negativeShiftIso m f).hom
    (ShiftedHom.comp f.hom
      (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
        (by omega : -n+0 = -n)) (by omega : -n+m=m-n))
    (by omega : -m+a=a-m) (by omega : (m-n)+ -m = -n)
    (by omega : (m-n)+ -m+a=a-n)]
  rw [← ShiftedHom.comp_assoc (negativeShiftIso m f).hom f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0 = -n))
    (by omega : m+ -m=0) (by omega : -n+m=m-n) (by omega : -n+m+ -m= -n)]
  rw [negativeShiftIso_comp_hom, ShiftedHom.mk₀_id_comp]
  have h := ShiftedHom.comp_assoc v (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
    (by omega : 0+a=a) (by omega : -n+0= -n) (by omega : -n+0+a=a-n)
  simpa only [ShiftedHom.comp_mk₀] using h

end ArExplicit

end

end OAI
