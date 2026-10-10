import OAI.Algebra.AuslanderReiten.HomComplex.FullHomZeroRepresentative

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ)

def fullHomPlainZeroEquiv : CohomologyClass K L 0 ≃ₗ[k]
    ((HomotopyCategory.quotient C _).obj K ⟶ (HomotopyCategory.quotient C _).obj L) :=
  (fullHomShiftedHomotopyEquiv k K L 0).trans
    (Linear.homCongr k (Iso.refl _)
      ((shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).app _))

theorem fullHomPlainZeroEquiv_mk (f : K ⟶ L) :
    fullHomPlainZeroEquiv k K L (CohomologyClass.mk (Cocycle.ofHom f)) =
      (HomotopyCategory.quotient C _).map f := by
  simp only [fullHomPlainZeroEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  change fullHomShiftedHomotopyEquiv k K L 0
    (CohomologyClass.mk (Cocycle.ofHom f)) ≫
      (shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).hom.app _ = _
  rw [← fullHomPrecomp_identity f, fullHomShiftedHomotopyEquiv_precomp]
  change (_ ≫ fullHomShiftedHomotopyEquiv k L L 0 (fullHomIdentity L)) ≫ _ = _
  erw [fullHomShiftedHomotopyEquiv_identity, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

theorem fullHomPlainZeroEquiv_identity :
    fullHomPlainZeroEquiv k K K (fullHomIdentity K) = 𝟙 _ := by
  rw [fullHomIdentity, fullHomPlainZeroEquiv_mk, CategoryTheory.Functor.map_id]

end ArExplicit

end

end OAI
