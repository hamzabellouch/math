import OAI.Algebra.AuslanderReiten.Homology.TriangleGradedSequence
import Mathlib.CategoryTheory.Shift.ShiftedHom

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleGradedSequence
universe u v w
variable (k : Type u) [CommRing k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
variable (T : Triangle C) (X : C)

theorem integerUnit_smul {M : Type*} [AddCommGroup M] [Module k M]
    (s : ℤˣ) (x : M) : s • x = x := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact one_smul _ x
  · change (-1 : ℤ) • x = x
    rw [neg_one_zsmul]
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← two_smul k, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]

theorem first_eq_shift (n : ℤ) (v : Bottom T X n) :
    first k T X n v = v ≫ T.mor₁⟦n⟧' := by
  change v ≫ (n.negOnePow • T.mor₁⟦n⟧') = _
  rw [integerUnit_smul k]

theorem second_eq_shift (n : ℤ) (v : Middle T X n) :
    second k T X n v = v ≫ T.mor₂⟦n⟧' := by
  change v ≫ (n.negOnePow • T.mor₂⟦n⟧') = _
  rw [integerUnit_smul k]

theorem nextIso_inv_first (n : ℤ) :
    (nextIso T n).inv.hom₁ =
      (CategoryTheory.shiftFunctorAdd' C n 1 (n+1) rfl).inv.app T.obj₁ := by
  simp [nextIso]
  rfl

theorem connecting_eq_product (n : ℤ) (v : Top T X n) :
    connecting k T X n v = ShiftedHom.comp v T.mor₃ (add_comm 1 n) := by
  change v ≫ ((n.negOnePow • T.mor₃⟦n⟧' ≫
    (CategoryTheory.shiftFunctorComm C 1 n).hom.app T.obj₁) ≫
      (nextIso T n).inv.hom₁) = _
  rw [integerUnit_smul k, nextIso_inv_first]
  simp only [ShiftedHom.comp,
    CategoryTheory.shiftFunctorComm_eq C 1 n (n+1) (add_comm 1 n),
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]
  rfl

end ArExplicit.TriangleGradedSequence

end

end OAI
