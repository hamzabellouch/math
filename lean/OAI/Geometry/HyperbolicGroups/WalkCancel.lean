import Mathlib
import OAI.Geometry.HyperbolicGroups.BigonRemove
import OAI.Geometry.HyperbolicGroups.EdgeMergeComponents
import OAI.Geometry.HyperbolicGroups.MergeWalk
import OAI.Geometry.HyperbolicGroups.StepChain
import OAI.Geometry.HyperbolicGroups.WalkCell

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma free_of_opposite {a b : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hab : P.index b = T.opposite (P.index a)) : T.free (T.kind (P.index b)) = true := by
  rw [hab,T.opposite_kind]; exact ha

lemma reverse_label {a b : P.Dart} (hab : P.index b = T.opposite (P.index a)) :
    T.label (P.index a) = T.rev (T.label (P.index b)) := by
  rw [hab,T.opposite_label,T.rev_rev]

def deletedBigon {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) : WalkPicture.{u} T := by
  let h : P.pairing.Bigon a (P.pairing.face a) :=
    ⟨(P.nonmonogon ha).symm,rfl,h₂⟩
  exact {
    Dart := {x : P.Dart // OffPair a (P.pairing.face a) x}
    pairing := h.remove
    index := P.index ∘ Subtype.val
    closed := h.remove_closed P.closed
    kind := h.remove_kind P.kind
    paired := (h.remove_respects P.respects (P.reverse_label (P.bigon_opposite ha h₂))).2
    genusZero := h.remove_genusZero P.genusZero }

lemma deletedBigon_retains {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) :
    Nonempty (P.Retains (P.deletedBigon ha h₂)) := by
  refine ⟨⟨Subtype.val,Subtype.val_injective,fun _ => rfl,fun _ _ => rfl,?_⟩⟩
  intro x hx
  have hxa : x ≠ a := by intro he; rw [he,ha] at hx; cases hx
  have hxb : x ≠ P.pairing.face a := by intro he; rw [he,P.free_face ha] at hx; cases hx
  exact ⟨⟨x,hxa,hxb⟩,rfl⟩

lemma deletedBigon_chain {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (h₂ : P.pairing.face (P.pairing.face a) = a) : (P.deletedBigon ha h₂).chain = P.chain := by
  change (∑ x : {x : P.Dart // OffPair a (P.pairing.face a) x}, T.weight (P.index x.val)) =
    ∑ x : P.Dart, T.weight (P.index x)
  apply sum_offPair (P.nonmonogon ha).symm (T.weight ∘ P.index)
  change T.weight (P.index a) + T.weight (P.index (P.pairing.face a)) = 0
  rw [P.bigon_opposite ha h₂]
  exact T.opposite_weight _ ha

lemma mergeSide {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    P.pairing.MergeSide a (P.pairing.edge a) :=
  ⟨rfl,hf,P.nonmonogon ha,P.nonmonogon (P.free_of_opposite ha hop)⟩

def cancelledSide {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) : WalkPicture.{u} T := by
  let h := P.mergeSide ha hop hf
  exact {
    Dart := {x : P.Dart // OffPair a (P.pairing.edge a) x}
    pairing := P.pairing.mergeEdge h
    index := P.index ∘ Subtype.val
    closed := PictureMap.mergeEdge_closed_local h P.closed
      (by change T.front (P.index a) = T.back (P.index (P.pairing.edge a)); rw [hop,T.opposite_back])
      (by change T.front (P.index (P.pairing.edge a)) = T.back (P.index a); rw [hop,T.opposite_front])
    kind := PictureMap.mergeEdge_kind h P.kind
      (by change T.kind (P.index a) = T.kind (P.index (P.pairing.edge a)); rw [hop,T.opposite_kind])
    paired := (PictureMap.mergeEdge_respects h P.respects).2
    genusZero := P.pairing.mergeEdge_genusZero h P.genusZero }

lemma cancelledSide_retains {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    Nonempty (P.Retains (P.cancelledSide ha hop hf)) := by
  refine ⟨⟨Subtype.val,Subtype.val_injective,fun _ => rfl,?_,?_⟩⟩
  · intro x hx
    exact PictureMap.mergeEdge_face_frozen (P.mergeSide ha hop hf) P.kind T.free ha
      (P.free_of_opposite ha hop) x hx
  · intro x hx
    have hxa : x ≠ a := by intro he; rw [he,ha] at hx; cases hx
    have hxb : x ≠ P.pairing.edge a := by
      intro he; rw [he,P.free_of_opposite ha hop] at hx; cases hx
    exact ⟨⟨x,hxa,hxb⟩,rfl⟩

lemma cancelledSide_chain {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    (P.cancelledSide ha hop hf).chain = P.chain := by
  change (∑ x : {x : P.Dart // OffPair a (P.pairing.edge a) x}, T.weight (P.index x.val)) =
    ∑ x : P.Dart, T.weight (P.index x)
  apply sum_offPair (P.pairing.edge_ne a).symm (T.weight ∘ P.index)
  change T.weight (P.index a) + T.weight (P.index (P.pairing.edge a)) = 0
  rw [hop]
  exact T.opposite_weight _ ha

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
