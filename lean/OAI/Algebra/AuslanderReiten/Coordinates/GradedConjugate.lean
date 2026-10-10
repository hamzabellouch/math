import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedConjugateAction

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m d : ℤ) (h : -n+m=d)
variable (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

def gradedConjugate : X ⟶ X⟦d⟧ :=
  ShiftedHom.comp f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0= -n)) h

theorem gradedConjugate_action (a : ℤ) (v : S ⟶ Z⟦a⟧) :
    ShiftedHom.comp (v ≫ c⟦a⟧') (negativeShiftIso n e).hom (by omega : -n+a=a-n) =
      ShiftedHom.comp
        (ShiftedHom.comp v (negativeShiftIso m f).hom (by omega : -m+a=a-m))
        (gradedConjugate n m d h e f c) (by omega : d+(a-m)=a-n) := by
  have hd : d=m-n := by omega
  revert h
  rw [hd]
  intro h
  exact shiftedConjugate_action n m e f c a v

theorem gradedConjugate_comp_hom :
    ShiftedHom.comp (gradedConjugate n m d h e f c) e.hom (by omega : n+d=m) =
      ShiftedHom.comp f.hom (ShiftedHom.mk₀ (0:ℤ) rfl c) (by omega : 0+m=m) := by
  unfold gradedConjugate
  rw [ShiftedHom.comp_assoc f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0= -n)) e.hom h (by omega : n+ -n=0) (by omega : n+ -n+m=m)]
  rw [ShiftedHom.comp_assoc (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom e.hom
    (by omega : -n+0= -n) (by omega : n+ -n=0) (by omega : n+ -n+0=0),
    negativeShiftIso_comp_hom, ShiftedHom.comp_mk₀_id]

theorem gradedConjugate_eq_of_square (p : X ⟶ X⟦d⟧)
    (hp : ShiftedHom.comp p e.hom (by omega : n+d=m) =
      ShiftedHom.comp f.hom (ShiftedHom.mk₀ (0:ℤ) rfl c) (by omega : 0+m=m)) :
    gradedConjugate n m d h e f c = p := by
  apply (cancel_mono (e.hom⟦d⟧' ≫
    (shiftFunctorAdd' C n d m (by omega)).inv.app Y)).mp
  change ShiftedHom.comp (gradedConjugate n m d h e f c) e.hom _ = ShiftedHom.comp p e.hom _
  rw [gradedConjugate_comp_hom]
  exact hp.symm

end ArExplicit

end

end OAI
