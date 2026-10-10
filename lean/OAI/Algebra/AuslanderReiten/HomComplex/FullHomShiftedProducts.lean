import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedHomotopy
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w

section Functor
variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
variable (F : C ⥤ D) [F.CommShift ℤ]
variable {X Y Z : C} {n m : ℤ}

theorem map_shifted_composition (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z⟦m⟧) :
    F.map (f ≫ g⟦n⟧' ≫ (CategoryTheory.shiftFunctorAdd' C m n (n+m) (add_comm m n)).inv.app Z) ≫
      (F.commShiftIso (n+m)).hom.app Z =
    (F.map f ≫ (F.commShiftIso n).hom.app Y) ≫
      (F.map g ≫ (F.commShiftIso m).hom.app Z)⟦n⟧' ≫
        (CategoryTheory.shiftFunctorAdd' D m n (n+m) (add_comm m n)).inv.app (F.obj Z) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (F.commShiftIso_add' (add_comm m n))) Z
  simp only [Functor.CommShift.isoAdd'_hom_app] at h
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc
    ((CategoryTheory.shiftFunctorAdd' C m n (n+m) (add_comm m n)).inv.app Z)
    ((CategoryTheory.shiftFunctorAdd' C m n (n+m) (add_comm m n)).hom.app Z),
    Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [F.commShiftIso_hom_naturality_assoc g n]

end Functor

variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem fullHomShiftedHomotopyEquiv_product (x : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomShiftedHomotopyEquiv k K M (n+m) (CompleteComparison.fullHomProduct x y) =
      fullHomShiftedHomotopyEquiv k K L n x ≫
        (fullHomShiftedHomotopyEquiv k L M m y)⟦n⟧' ≫
          (CategoryTheory.shiftFunctorAdd' (HomotopyCategory C (ComplexShape.up ℤ)) m n
            (n+m) (add_comm m n)).inv.app ((HomotopyCategory.quotient C _).obj M) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [CompleteComparison.fullHomProduct_mk, fullHomShiftedHomotopyEquiv_mk,
    fullHomShiftedHomotopyEquiv_mk, fullHomShiftedHomotopyEquiv_mk,
    CompleteComparison.cocycleHom_product]
  exact map_shifted_composition (HomotopyCategory.quotient C _)
    (Cocycle.equivHomShift.symm x) (Cocycle.equivHomShift.symm y)

end ArExplicit

end

end OAI
