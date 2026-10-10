import OAI.Algebra.AuslanderReiten.Coordinates.IteratedCubicCoordinates
import OAI.Algebra.AuslanderReiten.Coordinates.GradedConjugate
import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedCoordinateProducts

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)
variable {X S : C} (u : X ≅ Y 0) (c : ∀ n, Y (n+3) ⟶ Y n)

def coverCubic : X ⟶ X⟦(3 : ℤ)⟧ :=
  (basedIteration Y s u 3).hom ≫ (c 0 ≫ u.inv)⟦(3 : ℤ)⟧'

variable (hs : ∀ n, c n ≫ (s n).hom =
  (s (n+3)).hom ≫ (c (n+1))⟦(1 : ℤ)⟧')
include hs

theorem coverCubic_square (n : ℕ) :
    ShiftedHom.comp (coverCubic Y s u c) (basedIteration Y s u n).hom
        (by omega : (n : ℤ)+3=((n+3 : ℕ) : ℤ)) =
      ShiftedHom.comp (basedIteration Y s u (n+3)).hom
        (ShiftedHom.mk₀ (0 : ℤ) rfl (c n)) (by omega) := by
  have hn := iteratedShiftIso_natural (Y := fun j => Y (j+3))
    (s := fun j => s (j+3)) s c hs n
  have hbase : (c 0 ≫ u.inv) ≫ (basedIteration Y s u n).hom =
      (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom ≫
        (c n)⟦(n : ℤ)⟧' := by
    simpa only [basedIteration, Iso.trans_hom, Category.assoc,
      Iso.inv_hom_id_assoc] using hn
  erw [coverCubic, ← ShiftedHom.comp_mk₀ (basedIteration Y s u 3).hom (0 : ℤ) rfl (c 0 ≫ u.inv)]
  change ShiftedHom.comp
    (ShiftedHom.comp (basedIteration Y s u 3).hom
      (ShiftedHom.mk₀ (0 : ℤ) rfl (c 0 ≫ u.inv)) (by omega : (0 : ℤ)+3=3))
    (basedIteration Y s u n).hom _ = _
  rw [ShiftedHom.comp_assoc (basedIteration Y s u 3).hom
    (ShiftedHom.mk₀ (0 : ℤ) rfl (c 0 ≫ u.inv)) (basedIteration Y s u n).hom
    (by omega : (0 : ℤ)+3=3) (by omega : (n : ℤ)+0=n) (by omega),
    ShiftedHom.mk₀_comp, hbase]
  rw [basedIteration_three_hom Y s u n]
  rw [ShiftedHom.comp_assoc (basedIteration Y s u 3).hom
    (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
    (ShiftedHom.mk₀ (0 : ℤ) rfl (c n)) (by omega) (by omega : 0+(n : ℤ)=n) (by omega),
    ShiftedHom.comp_mk₀]

theorem coverCubic_eq_conjugate (n : ℕ) :
    gradedConjugate (n : ℤ) ((n+3 : ℕ) : ℤ) 3 (by omega)
      (basedIteration Y s u n) (basedIteration Y s u (n+3)) (c n) =
      coverCubic Y s u c :=
  gradedConjugate_eq_of_square _ _ _ _ _ _ _ _ (coverCubic_square Y s u c hs n)

theorem coverCubic_action (n : ℕ) (a : ℤ) (v : S ⟶ (Y (n+3))⟦a⟧) :
    ShiftedHom.comp (v ≫ (c n)⟦a⟧')
        (negativeShiftIso (n : ℤ) (basedIteration Y s u n)).hom (by omega) =
      ShiftedHom.comp
        (ShiftedHom.comp v
          (negativeShiftIso ((n+3 : ℕ) : ℤ) (basedIteration Y s u (n+3))).hom
          (by omega : -((n+3 : ℕ) : ℤ)+a=a-((n+3 : ℕ) : ℤ)))
        (coverCubic Y s u c) (by omega : 3+(a-((n+3 : ℕ) : ℤ))=a-(n : ℤ)) := by
  rw [← coverCubic_eq_conjugate Y s u c hs n]
  exact gradedConjugate_action _ _ _ _ _ _ _ a v

end ArExplicit

end

end OAI
