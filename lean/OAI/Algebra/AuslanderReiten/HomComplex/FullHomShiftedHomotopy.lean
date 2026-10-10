import OAI.Algebra.AuslanderReiten.Homology.TriangleHomExact

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def fullHomShiftedHomotopyEquiv : CohomologyClass K L n ≃ₗ[k]
    ((HomotopyCategory.quotient C _).obj K ⟶ ((HomotopyCategory.quotient C _).obj L)⟦n⟧) :=
  (fullHomHomotopyLinearEquiv k K L n).trans
    (Linear.homCongr k (Iso.refl _)
      (((HomotopyCategory.quotient C _).commShiftIso n).app L))

@[simp]
theorem fullHomShiftedHomotopyEquiv_mk (x : Cocycle K L n) :
    fullHomShiftedHomotopyEquiv k K L n (CohomologyClass.mk x) =
      (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) ≫
        (((HomotopyCategory.quotient C _).commShiftIso n).app L).hom := by
  simp only [fullHomShiftedHomotopyEquiv, LinearEquiv.trans_apply,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rfl

end ArExplicit

end

end OAI
