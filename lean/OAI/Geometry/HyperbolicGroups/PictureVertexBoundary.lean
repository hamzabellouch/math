import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureContact

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {X : Type*} (P : PictureMap X)
variable (apex selected : X → Bool) (radial : X → Prop)
variable (hface : ∀ x, selected (P.face x) = selected x)
  (hvertex : ∀ x, apex (P.vertex⁻¹ x) = apex x)
  (hrev : ∀ x, apex x = true → apex (P.edge x) = false)
  (hradial : ∀ x, apex x = true → radial x)
  (hedge : ∀ x, radial (P.edge x) ↔ radial x)

abbrev VertexTransition := {x : X // apex x = true ∧ selected x ≠ selected (P.vertex⁻¹ x)}

def transitionSide (x : P.VertexTransition apex selected) : X :=
  if selected x.val then P.edge (P.vertex⁻¹ x.val) else P.vertex⁻¹ x.val

lemma edge_previous_face (x : X) : P.face (P.edge (P.vertex⁻¹ x)) = x := by
  exact P.vertex.apply_symm_apply x

include hface in
lemma transition_previous_selected (x : X) : selected (P.edge (P.vertex⁻¹ x)) = selected x := by
  rw [← hface (P.edge (P.vertex⁻¹ x)),P.edge_previous_face]

include hface hvertex hradial hedge in
lemma transitionSide_properties (x : P.VertexTransition apex selected) :
    radial (P.transitionSide apex selected x) ∧
      selected (P.transitionSide apex selected x) = true ∧
      selected (P.edge (P.transitionSide apex selected x)) ≠ true := by
  have ha : apex (P.vertex⁻¹ x.val) = true := (hvertex _).trans x.property.1
  have hr : radial (P.vertex⁻¹ x.val) := hradial _ ha
  have he := P.transition_previous_selected selected hface x.val
  have hn := x.property.2
  unfold transitionSide
  cases hs : selected x.val with
  | true =>
    simp only [ite_true]
    refine ⟨(hedge _).mpr hr,he.trans hs,?_⟩
    rw [P.edge_edge]
    exact fun h => hn (hs.trans h.symm)
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have hy : selected (P.vertex⁻¹ x.val) = true := by
      cases hh : selected (P.vertex⁻¹ x.val)
      · exact False.elim (hn (hs.trans hh.symm))
      · rfl
    exact ⟨hr,hy,by rw [he,hs]; decide⟩

include hvertex hrev in
lemma transitionSide_recover (x : P.VertexTransition apex selected) :
    (if apex (P.transitionSide apex selected x) then P.transitionSide apex selected x
      else P.edge (P.transitionSide apex selected x)) = P.vertex⁻¹ x.val := by
  have ha : apex (P.vertex⁻¹ x.val) = true := (hvertex _).trans x.property.1
  have hb := hrev _ ha
  unfold transitionSide
  cases selected x.val <;> simp only [Bool.false_eq_true,ite_true,ite_false,ha,hb,P.edge_edge]

include hvertex hrev in
lemma transitionSide_injective : Function.Injective (P.transitionSide apex selected) := by
  intro x y he
  have h := congrArg (fun z => if apex z then z else P.edge z) he
  rw [P.transitionSide_recover apex selected hvertex hrev,
    P.transitionSide_recover apex selected hvertex hrev] at h
  exact Subtype.ext ((P.vertex⁻¹).injective h)

variable [Fintype X]

include hface hvertex hrev hradial hedge in
/-- Every change of selection at an apex link charges a distinct actual
radial boundary side. The two orientations are handled by the unique apex end. -/
theorem vertex_transitions_le_boundary : Fintype.card (P.VertexTransition apex selected) ≤
    Fintype.card (P.BoundarySide (fun x => selected x = true) radial) := by
  let g : P.VertexTransition apex selected → P.BoundarySide (fun x => selected x = true) radial :=
    fun x => ⟨P.transitionSide apex selected x,
      P.transitionSide_properties apex selected radial hface hvertex hradial hedge x⟩
  apply Fintype.card_le_of_injective g
  intro x y h
  exact P.transitionSide_injective apex selected hvertex hrev (congrArg Subtype.val h)

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

section

end
end

end OAI
