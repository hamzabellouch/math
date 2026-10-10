import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMapFurther
import OAI.Geometry.HyperbolicGroups.PermErasePair
import OAI.Geometry.HyperbolicGroups.GeneralSwitch
import OAI.Geometry.HyperbolicGroups.FaceWalk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
namespace PictureMap
variable {M : PictureMap D} {a b : D}

structure Bigon (a b : D) : Prop where
  ne : a ≠ b
  forward : M.face a = b
  backward : M.face b = a

namespace Bigon
variable (h : M.Bigon a b)
include h

lemma face_invariant (x : D) : OffPair a b (M.face x) ↔ OffPair a b x := by
  have h₁ : M.face x = a ↔ x = b := by rw [← h.backward]; exact M.face.apply_eq_iff_eq
  have h₂ : M.face x = b ↔ x = a := by rw [← h.forward]; exact M.face.apply_eq_iff_eq
  simp only [OffPair,ne_eq,h₁,h₂,and_comm]

lemma switching_vertex : M.vertex.SameCycle a (M.edge b) := by
  have hh : M.vertex (M.edge b) = a := by rw [vertex,mul_apply,M.edge_edge,h.backward]
  exact (hh ▸ (SameCycle.rfl (x := M.edge b)).apply_right).symm

variable [DecidableEq D]

lemma switched_pair : (M.switch a (M.edge b)).edge a = b := by
  change swap a (M.edge b) (M.edge (swap a (M.edge b) a)) = b
  rw [swap_apply_left,M.edge_edge,swap_apply_of_ne_of_ne h.ne.symm (M.edge_ne b).symm]

lemma switched_back : (M.switch a (M.edge b)).edge b = a := by
  have hh := congrArg (M.switch a (M.edge b)).edge h.switched_pair
  simpa only [edge_edge] using hh.symm

lemma edge_invariant (x : D) : OffPair a b ((M.switch a (M.edge b)).edge x) ↔ OffPair a b x := by
  have h₁ : (M.switch a (M.edge b)).edge x = a ↔ x = b := by
    simpa only [h.switched_back] using ((M.switch a (M.edge b)).edge.apply_eq_iff_eq (x := x) (y := b))
  have h₂ : (M.switch a (M.edge b)).edge x = b ↔ x = a := by
    simpa only [h.switched_pair] using ((M.switch a (M.edge b)).edge.apply_eq_iff_eq (x := x) (y := a))
  simp only [OffPair,ne_eq,h₁,h₂,and_comm]

/-- The zero-chain backtracking bigon is first pinched off by a legal vertex
switch and then deleted as a whole component. Its other edge contacts need
not initially meet one another. -/
def remove : PictureMap {x // OffPair a b x} :=
  (M.switch a (M.edge b)).restrict (OffPair a b) h.face_invariant h.edge_invariant

lemma remove_face (x : {x // OffPair a b x}) : (h.remove.face x).val = M.face x.val := rfl

lemma remove_genusZero [Fintype D] (hG : M.GenusZero) : h.remove.GenusZero := by
  exact (M.switch a (M.edge b)).restrict_genusZero (OffPair a b)
    (M.switch_genusZero_general hG a (M.edge b) h.switching_vertex)
    h.face_invariant h.edge_invariant

lemma remove_respects {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) (hab : label a = rev (label b)) :
    h.remove.Respects (label ∘ Subtype.val) start rev := by
  have hs := switch_respects hM (a := a) (b := M.edge b) (hab.trans (hM.2 b).symm)
  exact ⟨fun x => hs.1 x.val,fun x => hs.2 x.val⟩

lemma remove_closed {V : Type*} {source target : D → V}
    (hc : M.FaceClosed source target) : h.remove.FaceClosed (source ∘ Subtype.val) (target ∘ Subtype.val) :=
  fun x => hc x.val

lemma remove_kind {C : Type*} {kind : D → C} (hk : M.FaceKind kind) :
    h.remove.FaceKind (kind ∘ Subtype.val) := fun x => hk x.val

end Bigon
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
