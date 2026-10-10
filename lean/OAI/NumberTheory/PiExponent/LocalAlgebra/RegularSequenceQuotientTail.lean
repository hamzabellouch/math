import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Regular.RegularSequence

namespace OAI

noncomputable section
namespace PiExponentJets.RegularSequenceQuotientTail
open RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R]

theorem principal_image_eq_scalar_top (I : Ideal R) (r : R) :
    Submodule.map I.mkQ (Ideal.span ({r} : Set R)) = r • (⊤ : Submodule R (R ⧸ I)) := by
  have h : r • (⊤ : Ideal R) = Ideal.span ({r} : Set R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← h, Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]

def quotientTailEquiv (I : Ideal R) (r : R) :
    QuotSMulTop r (R ⧸ I) ≃ₗ[R] R ⧸ (I ⊔ Ideal.span ({r} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (principal_image_eq_scalar_top I r).symm).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span ({r} : Set R)))

@[simp] theorem quotientTailEquiv_mk (I : Ideal R) (r a : R) :
    quotientTailEquiv I r (Submodule.Quotient.mk (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span ({r} : Set R)) a := rfl

theorem regular_quotient_cons_iff (I : Ideal R) (r : R) (rs : List R) :
    IsRegular (R ⧸ I) (r :: rs) ↔
      IsSMulRegular (R ⧸ I) r ∧
        IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs := by
  rw [isRegular_cons_iff]
  exact and_congr_right' ((quotientTailEquiv I r).isRegular_congr rs)

theorem regular_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsRegular (R ⧸ I) (r :: rs)) :
    IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs :=
  ((regular_quotient_cons_iff I r rs).mp h).2

theorem weaklyRegular_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsWeaklyRegular (R ⧸ I) (r :: rs)) :
    IsWeaklyRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs := by
  exact ((quotientTailEquiv I r).isWeaklyRegular_congr rs).mp
    ((isWeaklyRegular_cons_iff (R ⧸ I) r rs).mp h).2

theorem regular_map_quotient_iff (I : Ideal R) (rs : List R) :
    IsRegular (R ⧸ I) (rs.map (Ideal.Quotient.mk I)) ↔
      IsRegular (R ⧸ I) rs := by
  symm
  apply (AddEquiv.refl (R ⧸ I)).isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  induction z using Submodule.Quotient.induction_on with
  | H z => rfl

theorem regular_mapped_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsRegular (R ⧸ I) ((r :: rs).map (Ideal.Quotient.mk I))) :
    IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R)))
      (rs.map (Ideal.Quotient.mk (I ⊔ Ideal.span ({r} : Set R)))) := by
  apply (regular_map_quotient_iff _ _).mpr
  exact regular_quotient_tail I r rs ((regular_map_quotient_iff I (r :: rs)).mp h)

end PiExponentJets.RegularSequenceQuotientTail

end

end OAI
