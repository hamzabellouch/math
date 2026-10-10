import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralizeContractor
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentContractorEndgame

namespace OAI

/-! # The finiteness endgame from one contracting element

For a nilpotent-by-abelian-by-finite group it suffices to find any contracting
element on the nilpotent abelianization. A positive power enters the abelian
normal subgroup of the quotient; finite conjugation averaging then supplies
the central contractor needed for the finiteness argument.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G]

def normalAbelianizationAction (N : Subgroup G) [N.Normal] :
    G ⧸ N →* MulAut (Abelianization N) :=
  QuotientGroup.lift N
    ((characteristicQuotientAut (commutator N)).comp (MulAut.conjNormal (H := N))) (by
      intro n hn
      change characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) n) = 1
      have h := quotient_conjugation_pow_eq_one N n 1 (by simpa only [pow_one] using hn)
      simpa only [pow_one] using h)

@[simp] theorem normalAbelianizationAction_mk (N : Subgroup G) [N.Normal] (g : G) :
    normalAbelianizationAction N ((QuotientGroup.mk' N) g) =
      characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) g) := rfl

theorem virtualSolvableFiniteDimension_of_abelianByFinite_contractor [Group.FG G]
    (N : Subgroup G) [N.Normal] [Group.IsNilpotent N]
    (H : Subgroup (G ⧸ N)) [H.Normal] [H.FiniteIndex] [IsMulCommutative H]
    (t : G)
    (hbase : HasFinitelyGeneratedAscendingBase
      (characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t))) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  have ht : HasFinitelyGeneratedAscendingBase
      (normalAbelianizationAction N ((QuotientGroup.mk' N) t)) := hbase
  obtain ⟨x, hxcentral, hxbase⟩ := exists_central_ascending_contractor_of_finiteIndex
    H (normalAbelianizationAction N) ((QuotientGroup.mk' N) t) ht
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective N x
  rw [← hu, normalAbelianizationAction_mk] at hxbase
  rw [← hu] at hxcentral
  let : Group.FG (G ⧸ N) := Group.fg_of_surjective (QuotientGroup.mk'_surjective N)
  have hQ : IsVirtuallyPolycyclic (G ⧸ N) :=
    ⟨H, inferInstance, isPolycyclic_of_finitelyGenerated_commGroup H⟩
  exact virtualSolvableFiniteDimension_of_nilpotent_abelian_contractor N u hxcentral hxbase hQ

end PolycyclicRecognition

end

end OAI
