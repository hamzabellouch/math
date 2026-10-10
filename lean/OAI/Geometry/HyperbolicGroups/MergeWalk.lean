import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PermErasePair
import OAI.Geometry.HyperbolicGroups.FaceWalk
import OAI.Geometry.HyperbolicGroups.EdgeMerge

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D C L V : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable {M : PictureMap D} {a b : D} (h : M.MergeSide a b)

lemma mergeEdge_respects {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) :
    (M.mergeEdge h).Respects (label ∘ Subtype.val) start rev := by
  constructor
  · intro x
    have hc : M.vertex.SameCycle x.val ((M.mergeEdge h).vertex x).val := by
      apply (erasePair_orbits M.vertex h.ne x ((M.mergeEdge h).vertex x)).mp
      rw [← M.mergeEdge_vertex h]
      exact SameCycle.rfl.apply_right
    exact ((sameCycle_le_of_apply (s := Setoid.ker (start ∘ label))
      (fun x => (hM.1 x).symm)) hc).symm
  · intro x
    exact hM.2 x.val

lemma mergeEdge_kind {kind : D → C} (hk : M.FaceKind kind) (hab : kind a = kind b) :
    (M.mergeEdge h).FaceKind (kind ∘ Subtype.val) := by
  intro x
  have hc : (M.splice a b).face.SameCycle x.val ((M.mergeEdge h).face x).val := by
    exact (erasePair_orbits (M.face * swap a b) h.ne x ((M.mergeEdge h).face x)).mp SameCycle.rfl.apply_right
  exact (kind_cycle (splice_kind hk hab) hc).symm

omit [Fintype D] in
lemma mergeEdge_face_of_away (x : {x // OffPair a b x})
    (ha : M.face x.val ≠ a) (hb : M.face x.val ≠ b) :
    ((M.mergeEdge h).face x).val = M.face x.val := by
  change bypass (bypass (M.face * swap a b) a) b x.val = M.face x.val
  rw [bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
  simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,ite_eq_right ha,ite_eq_right hb]

omit [Fintype D] in
lemma mergeEdge_face_hit_left (x : {x // OffPair a b x})
    (hx : M.face x.val = a) : ((M.mergeEdge h).face x).val = M.face b := by
  change bypass (bypass (M.face * swap a b) a) b x.val = M.face b
  rw [bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
  simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,hx,ite_eq_left,
    swap_apply_left,ite_eq_right h.right_nonmonogon]

omit [Fintype D] in
lemma mergeEdge_face_hit_right (x : {x // OffPair a b x})
    (hx : M.face x.val = b) : ((M.mergeEdge h).face x).val = M.face a := by
  change bypass (bypass (M.face * swap a b) a) b x.val = M.face a
  rw [bypass_away _ _ _ x.property.2,bypass_away _ _ _ x.property.1]
  simp only [mul_apply,swap_apply_of_ne_of_ne x.property.1 x.property.2,hx,ite_eq_right h.ne.symm,ite_eq_left]
  exact h.crossed_b

omit [Fintype D] in
/-- Closure in indexed template vertices is retained even though adjacent
polygons belonging to OTHER occurrences use different template vertex types.
Only the two cancelling sides need agree as opposite template steps. -/
lemma mergeEdge_closed_local {source target : D → V} (hc : M.FaceClosed source target)
    (ha : source a = target b) (hb : source b = target a) :
    (M.mergeEdge h).FaceClosed (source ∘ Subtype.val) (target ∘ Subtype.val) := by
  intro x
  change source ((M.mergeEdge h).face x).val = target x.val
  by_cases hxa : M.face x.val = a
  · rw [mergeEdge_face_hit_left h x hxa,hc,← ha]
    exact (congrArg source hxa).symm.trans (hc x.val)
  by_cases hxb : M.face x.val = b
  · rw [mergeEdge_face_hit_right h x hxb,hc,← hb]
    exact (congrArg source hxb).symm.trans (hc x.val)
  · rw [mergeEdge_face_of_away h x hxa hxb,hc]

omit [Fintype D] in
/-- Any frozen kind disjoint from the cancelled kind retains its complete
face cycles and side indices under the common-side cancellation. -/
lemma mergeEdge_face_frozen {kind : D → C} (hk : M.FaceKind kind)
    (free : C → Bool) (ha : free (kind a) = true) (hb : free (kind b) = true)
    (x : {x // OffPair a b x}) (hx : free (kind x.val) = false) :
    ((M.mergeEdge h).face x).val = M.face x.val := by
  apply mergeEdge_face_of_away h x
  · intro he
    have hh := congrArg free (hk x.val)
    rw [he,ha,hx] at hh
    cases hh
  · intro he
    have hh := congrArg free (hk x.val)
    rw [he,hb,hx] at hh
    cases hh

/-- Closed target face walks remain closed after deleting the common side.
This uses only edge reversal and original closure, and is unaffected by any
other common vertices or edges of the two polygons. -/
lemma mergeEdge_closed {source target : D → V} (hc : M.FaceClosed source target)
    (he : ∀ x, source (M.edge x) = target x) :
    (M.mergeEdge h).FaceClosed (source ∘ Subtype.val) (target ∘ Subtype.val) := by
  have hv : ∀ x, source (M.vertex x) = source x := by
    intro x
    change source (M.face (M.edge x)) = source x
    rw [hc,← he,M.edge_edge]
  intro x
  let y := (M.mergeEdge h).edge x
  have hcyc : M.vertex.SameCycle y.val ((M.mergeEdge h).vertex y).val := by
    apply (erasePair_orbits M.vertex h.ne y ((M.mergeEdge h).vertex y)).mp
    rw [← M.mergeEdge_vertex h]
    exact SameCycle.rfl.apply_right
  have hs := (sameCycle_le_of_apply (s := Setoid.ker source) (fun x => (hv x).symm)) hcyc
  have hface : (M.mergeEdge h).vertex y = (M.mergeEdge h).face x := by
    change (M.mergeEdge h).face ((M.mergeEdge h).edge ((M.mergeEdge h).edge x)) = _
    rw [edge_edge]
  change source ((M.mergeEdge h).face x).val = target x.val
  rw [hface] at hs
  exact hs.symm.trans (he x.val)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
