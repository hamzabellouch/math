import OAI.Algebra.AuslanderReiten.Coordinates.IteratedShiftAddition

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)

theorem iteratedShiftIso_three_hom (n : ℕ) :
    (iteratedShiftIso Y s (n+3)).hom =
      ShiftedHom.comp (iteratedShiftIso Y s 3).hom
        (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
          (by omega : (n:ℤ)+3=((n+3:ℕ):ℤ)) := by
  induction n with
  | zero =>
    have hz : (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) 0).hom =
        ShiftedHom.mk₀ (0:ℤ) rfl (𝟙 (Y 3)) := by
      simp only [iteratedShiftIso, ShiftedHom.mk₀, shiftFunctorZero',
        eqToIso_refl, Iso.refl_trans, Category.id_comp]
      rfl
    rw [hz]
    exact (ShiftedHom.comp_mk₀_id _ 0 rfl).symm
  | succ n ih =>
    change (iteratedShiftIso Y s ((n+3)+1)).hom = _
    rw [iteratedShiftIso_succ_hom, ih, iteratedShiftIso_succ_hom]
    exact ShiftedHom.comp_assoc (iteratedShiftIso Y s 3).hom
      (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
      (s (n+3)).hom (by omega) (by omega) (by omega)

variable {X : C} (u : X ≅ Y 0)

def basedIteration (n : ℕ) : X ≅ (Y n)⟦(n:ℤ)⟧ := u ≪≫ iteratedShiftIso Y s n

theorem basedIteration_three_hom (n : ℕ) :
    (basedIteration Y s u (n+3)).hom =
      ShiftedHom.comp (basedIteration Y s u 3).hom
        (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
          (by omega : (n:ℤ)+3=((n+3:ℕ):ℤ)) := by
  change u.hom ≫ (iteratedShiftIso Y s (n+3)).hom = _
  rw [iteratedShiftIso_three_hom]
  simp only [basedIteration, Iso.trans_hom, ShiftedHom.comp, Category.assoc]

end ArExplicit

end

end OAI
