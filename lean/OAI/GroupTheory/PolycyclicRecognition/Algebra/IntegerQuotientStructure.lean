import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientCoordinates
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace OAI

/-! # The actual infinite cyclic quotient determined by a height homomorphism -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerQuotientEquiv : G ⧸ q.ker ≃* Multiplicative ℤ :=
  QuotientGroup.quotientKerEquivOfRightInverse q (fun z => t ^ z.toAdd) (by
    intro z
    apply Multiplicative.toAdd.injective
    simp [map_zpow, ht])

@[simp] theorem integerQuotientEquiv_mk (g : G) :
    integerQuotientEquiv q t ht (QuotientGroup.mk' q.ker g) = q g := rfl

include ht in
theorem integerQuotient_isCyclic : IsCyclic (G ⧸ q.ker) :=
  isCyclic_of_injective (integerQuotientEquiv q t ht).toMonoidHom
    (integerQuotientEquiv q t ht).injective

include ht in
theorem integerQuotient_infinite : Infinite (G ⧸ q.ker) :=
  Infinite.of_injective (integerQuotientEquiv q t ht).symm
    (integerQuotientEquiv q t ht).symm.injective

include ht in
theorem integerQuotient_generator (x : G ⧸ q.ker) :
    x ∈ Subgroup.zpowers (QuotientGroup.mk' q.ker t) := by
  refine ⟨(integerQuotientEquiv q t ht x).toAdd, ?_⟩
  apply (integerQuotientEquiv q t ht).injective
  rw [map_zpow, integerQuotientEquiv_mk, ht]
  apply Multiplicative.toAdd.injective
  simp

end PolycyclicRecognition

end

end OAI
