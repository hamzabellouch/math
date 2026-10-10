import OAI.Algebra.AuslanderReiten.Coordinates.IteratedShiftNaturality
import Mathlib.CategoryTheory.Shift.ShiftedHom

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)

theorem iteratedShiftIso_succ_hom (n : ℕ) :
    (iteratedShiftIso Y s (n+1)).hom =
      ShiftedHom.comp (iteratedShiftIso Y s n).hom (s n).hom
        (by omega : 1+(n:ℤ)=((n+1:ℕ):ℤ)) := rfl

theorem iteratedShiftIso_add_hom (m n : ℕ) :
    (iteratedShiftIso Y s (m+n)).hom =
      ShiftedHom.comp (iteratedShiftIso Y s m).hom
        (iteratedShiftIso (fun j => Y (m+j)) (fun j => s (m+j)) n).hom
          (by omega : (n:ℤ)+(m:ℤ)=((m+n:ℕ):ℤ)) := by
  induction n with
  | zero =>
    have hz : (iteratedShiftIso (fun j => Y (m+j)) (fun j => s (m+j)) 0).hom =
        ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 (Y m)) := by
      simp only [iteratedShiftIso, ShiftedHom.mk₀, shiftFunctorZero',
        eqToIso_refl, Iso.refl_trans, Category.id_comp]
      rfl
    rw [hz]
    exact (ShiftedHom.comp_mk₀_id _ 0 rfl).symm
  | succ n ih =>
    change (iteratedShiftIso Y s ((m+n)+1)).hom = _
    rw [iteratedShiftIso_succ_hom, ih, iteratedShiftIso_succ_hom]
    exact ShiftedHom.comp_assoc (iteratedShiftIso Y s m).hom
      (iteratedShiftIso (fun j => Y (m+j)) (fun j => s (m+j)) n).hom
      (s (m+n)).hom (by omega) (by omega) (by omega)

end ArExplicit

end

end OAI
