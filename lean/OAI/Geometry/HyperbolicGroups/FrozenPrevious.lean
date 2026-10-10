import Mathlib
import OAI.Geometry.HyperbolicGroups.FrozenWalk
import OAI.Geometry.HyperbolicGroups.WalkClasses

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.WalkPicture
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma free_previous {x : P.Dart} :
    T.free (T.kind (P.index (P.pairing.face⁻¹ x))) = T.free (T.kind (P.index x)) := by
  have h := congrArg T.free (P.kind (P.pairing.face⁻¹ x))
  simpa only [Function.comp_apply,Perm.inv_def,apply_symm_apply] using h.symm

lemma frozen_previous_index (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x : P.Dart} (hx : T.free (T.kind (P.index x)) = false) :
    P.index (P.pairing.face⁻¹ x) = B.next⁻¹ (P.index x) := by
  have hy : T.free (T.kind (P.index (P.pairing.face⁻¹ x))) = false := P.free_previous.trans hx
  have h := hm.commute ⟨P.pairing.face⁻¹ x,hy⟩
  change P.index (P.pairing.face (P.pairing.face⁻¹ x)) = B.next (P.index (P.pairing.face⁻¹ x)) at h
  apply B.next.injective
  simpa only [Perm.inv_def,apply_symm_apply] using h.symm

lemma faceClass_apply (x : P.Dart) : P.faceClass (P.pairing.face x) = P.faceClass x :=
  P.faceClass_eq.mpr (SameCycle.rfl.apply_left)
lemma faceClass_previous (x : P.Dart) : P.faceClass (P.pairing.face⁻¹ x) = P.faceClass x :=
  P.faceClass_eq.mpr (sameCycle_inv.mp (SameCycle.rfl.apply_left))

end HyperbolicObstruction.PictureSwitch.WalkPicture
end
end

section

end
end

end OAI
