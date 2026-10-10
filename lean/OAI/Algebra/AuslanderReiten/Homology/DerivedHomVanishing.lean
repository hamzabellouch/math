import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
open CochainComplex.HomComplex

def fullCohomologyDerivedEquiv (K L : CochainComplex C ℤ) (n : ℤ) [K.IsKProjective] :
    CohomologyClass K L n ≃ (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  CohomologyClass.homAddEquiv.toEquiv.trans
    ((Equiv.ofBijective DerivedCategory.Qh.map
      (CochainComplex.IsKProjective.Qh_map_bijective K
        ((HomotopyCategory.quotient C _).obj (L⟦n⟧)))).trans
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
        (((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧)) ≪≫
          (DerivedCategory.Q.commShiftIso n).app L)))

theorem derivedHom_zero_of_cochain_zero (K L : CochainComplex C ℤ) (n : ℤ)
    [K.IsKProjective] (h : ∀ a : Cochain K L n, a = 0)
    (f : DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) : f = 0 := by
  have hc : ∀ a : CohomologyClass K L n, a = 0 := by
    intro a
    obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective a
    have hb : b = 0 := Subtype.ext (h b.val)
    rw [hb, CohomologyClass.mk_zero]
  have : Subsingleton (CohomologyClass K L n) := ⟨fun a b => (hc a).trans (hc b).symm⟩
  exact (fullCohomologyDerivedEquiv K L n).symm.injective (Subsingleton.elim _ _)

end ArExplicit

end

end OAI
