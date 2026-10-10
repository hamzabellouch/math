import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedHomotopy
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComposition

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)

theorem fullHomShiftedHomotopyEquiv_postcomp (f : L ⟶ M) (x : CohomologyClass K L n) :
    fullHomShiftedHomotopyEquiv k K M n (fullHomPostcomp f n x) =
      fullHomShiftedHomotopyEquiv k K L n x ≫
        ((HomotopyCategory.quotient C _).map f)⟦n⟧' := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPostcomp_mk, fullHomShiftedHomotopyEquiv_mk,
    fullHomShiftedHomotopyEquiv_mk, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp, Category.assoc]
  simpa only [Category.assoc, Iso.app_hom] using congrArg
    (fun g => (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) ≫ g)
    ((HomotopyCategory.quotient C _).commShiftIso_hom_naturality f n)

theorem fullHomShiftedHomotopyEquiv_precomp (f : K ⟶ L) (x : CohomologyClass L M n) :
    fullHomShiftedHomotopyEquiv k K M n (fullHomPrecomp f n x) =
      (HomotopyCategory.quotient C _).map f ≫ fullHomShiftedHomotopyEquiv k L M n x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPrecomp_mk, fullHomShiftedHomotopyEquiv_mk,
    fullHomShiftedHomotopyEquiv_mk, Cocycle.equivHomShift_symm_precomp,
    Functor.map_comp, Category.assoc]
end ArExplicit

end

end OAI
