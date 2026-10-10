import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularDualRepresentation

namespace OAI

/-! # Maps from a cokernel as an integral kernel module -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

private def cokernelHomAddEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G) :
    (cokernel f ⟶ A) ≃+ LinearMap.ker (Linear.leftComp ℤ A f) where
  toFun h := ⟨cokernel.π f ≫ h, by
    change f ≫ (cokernel.π f ≫ h) = 0
    simp⟩
  invFun h := cokernel.desc f h.val (by exact h.property)
  left_inv h := by
    apply (cancel_epi (cokernel.π f)).mp
    change cokernel.π f ≫ cokernel.desc f (cokernel.π f ≫ h) _ = _
    exact cokernel.π_desc _ _ _
  right_inv h := by
    apply Subtype.ext
    change cokernel.π f ≫ cokernel.desc f h.val _ = h.val
    exact cokernel.π_desc _ _ _
  map_add' h k := by
    apply Subtype.ext
    change cokernel.π f ≫ (h + k) = cokernel.π f ≫ h + cokernel.π f ≫ k
    exact Rep.comp_add _ _ _

def cokernelHomModuleEquiv {P Q : Rep ℤ G} (f : P ⟶ Q) (A : Rep ℤ G) :
    (cokernel f ⟶ A) ≃ₗ[ℤ] LinearMap.ker (Linear.leftComp ℤ A f) where
  __ := cokernelHomAddEquiv f A
  map_smul' r h := map_intCast_smul (cokernelHomAddEquiv f A) ℤ ℤ r h

end PolycyclicRecognition

end

end OAI
