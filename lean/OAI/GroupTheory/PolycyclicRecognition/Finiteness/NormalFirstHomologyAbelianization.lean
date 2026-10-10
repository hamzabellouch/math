import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FirstHomologyAbelianizationNaturality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyModuleFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalAbelianizationQuotient

namespace OAI

/-! # The actual quotient action on first homology is abelianization

The comparison intertwines ambient conjugation, including for a nonabelian
normal subgroup. It identifies the first-homology representation used to
control the rank of a nilpotent normal subgroup.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem normalAbelianizationRepresentation_map (g : G) :
    normalAbelianizationRepresentation N g =
      (Abelianization.map (MulAut.conjNormal (H := N) g).toMonoidHom).toAdditive.toIntLinearMap := by
  apply LinearMap.ext
  intro a
  induction a using QuotientGroup.induction_on with | H a => rfl

def normalFirstHomologyAbelianizationIso :
    quotientHomologyAction N (trivialIntegral G) 1 ≅
      Rep.of (normalQuotientAbelianizationRepresentation N) := by
  let e : (quotientHomologyAction N (trivialIntegral G) 1).V ≃ₗ[ℤ]
      Additive (Abelianization N) := integralH1AbelianizationEquiv
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  apply LinearMap.ext
  intro x
  change e (normalHomologyMap ℤ N (trivialIntegral G) 1 g x) =
    normalAbelianizationRepresentation N g (e x)
  rw [normalAbelianizationRepresentation_map]
  exact integralH1AbelianizationEquiv_natural
    (MulAut.conjNormal (H := N) g).toMonoidHom x

end PolycyclicRecognition

end

end OAI
