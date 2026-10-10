import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFanCorner

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma walk_vertex_inverse (x : P.Dart) :
    P.pairing.vertex⁻¹ x = P.pairing.edge (P.pairing.face⁻¹ x) := by
  apply P.pairing.vertex.injective
  rw [Perm.inv_def,apply_symm_apply]
  change x = P.pairing.face (P.pairing.edge (P.pairing.edge (P.pairing.face⁻¹ x)))
  rw [P.pairing.edge_edge,Perm.inv_def,apply_symm_apply]

lemma walk_index_previous (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (x : P.Dart) (hx : walkFree n w d (walkKind n w d (P.index x)) = false) :
    P.index (P.pairing.face⁻¹ x) = (walkFrozenTarget n w d c hc f).next⁻¹ (P.index x) := by
  have he : walkFree n w d (walkKind n w d (P.index (P.pairing.face⁻¹ x))) = false := by
    have hk := P.kind (P.pairing.face⁻¹ x)
    rw [Perm.inv_def,apply_symm_apply] at hk
    change walkKind n w d (P.index x) = walkKind n w d (P.index (P.pairing.face⁻¹ x)) at hk
    rw [← hk]; exact hx
  apply (walkFrozenTarget n w d c hc f).next.injective
  have hh := (hm.commute ⟨P.pairing.face⁻¹ x,he⟩).symm
  change (walkFrozenTarget n w d c hc f).next (P.index (P.pairing.face⁻¹ x)) =
    P.index (P.pairing.face (P.pairing.face⁻¹ x)) at hh
  simpa only [Perm.inv_def,apply_symm_apply] using hh

lemma walk_corner_incoming (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = frozenCorner n w d g o) :
    walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)) = cornerIn n w g o := by
  rw [walk_vertex_inverse]
  have hh := P.paired (P.pairing.face⁻¹ x)
  change walkLabel n w d (P.index (P.pairing.edge (P.pairing.face⁻¹ x))) =
    rev n w (walkLabel n w d (P.index (P.pairing.face⁻¹ x))) at hh
  rw [hh,walk_index_previous n w d c hc f P hm x (by rw [hx]; rfl),hx,
    frozenCorner_previous]

lemma walk_triangle_bipartite (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = frozenCorner n w d g o) :
    dartPart n w (walkLabel n w d (P.index x)) ≠
      dartPart n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ x))) := by
  rw [walk_corner_incoming n w d c hc f P hm hx,hx,frozenCorner_label]
  exact corner_bipartite n w g o

lemma walk_triangle_inverse_no_two (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) {x : P.Dart} {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index (P.pairing.vertex⁻¹ x) = frozenCorner n w d h p) :
    P.pairing.vertex⁻¹ (P.pairing.vertex⁻¹ x) ≠ x := by
  intro he
  have hn := walk_corner_no_two_step n w d c hc f P hm hred hy
    (by rw [Perm.inv_def,apply_symm_apply]; exact hx)
  rw [Perm.inv_def,apply_symm_apply] at hn
  have hh := congrArg P.pairing.vertex he
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact hn hh.symm

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
