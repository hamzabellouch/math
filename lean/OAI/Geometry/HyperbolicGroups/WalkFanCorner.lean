import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFrozenTarget
import OAI.Geometry.HyperbolicGroups.ConeFanCorner
import OAI.Geometry.HyperbolicGroups.FullWalkNormal

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

lemma walk_start_link_constant {x y : P.Dart} (h : P.pairing.vertex.SameCycle x y) :
    start n w (walkLabel n w d (P.index x)) = start n w (walkLabel n w d (P.index y)) := by
  exact (sameCycle_le_of_apply
    (s := Setoid.ker (fun x => start n w (walkLabel n w d (P.index x))))
    (fun x => (P.respects.1 x).symm)) h

lemma walk_index_edge_previous (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (x : P.Dart) (hy : walkFree n w d (walkKind n w d (P.index (P.pairing.vertex x))) = false) :
    P.index (P.pairing.edge x) =
      (walkFrozenTarget n w d c hc f).next⁻¹ (P.index (P.pairing.vertex x)) := by
  have he : walkFree n w d (walkKind n w d (P.index (P.pairing.edge x))) = false := by
    have hk := P.kind (P.pairing.edge x)
    change walkKind n w d (P.index (P.pairing.vertex x)) =
      walkKind n w d (P.index (P.pairing.edge x)) at hk
    rw [← hk]; exact hy
  apply (walkFrozenTarget n w d c hc f).next.injective
  simp only [Perm.inv_def,apply_symm_apply]
  exact (hm.commute ⟨P.pairing.edge x,he⟩).symm

variable {c hc f}
def frozenCorner (g : FanTriangle n w) (o : Bool) : WalkStep n w d :=
  .inr ⟨.inl g,o,if o then (0 : Fin 3) else (2 : Fin 3)⟩

lemma frozenCorner_label (g : FanTriangle n w) (o : Bool) :
    walkLabel n w d (frozenCorner n w d g o) = cornerOut n w g o := by
  cases o <;> rfl

lemma frozenCorner_previous (g : FanTriangle n w) (o : Bool) :
    rev n w (walkLabel n w d ((walkFrozenTarget n w d c hc f).next⁻¹
      (frozenCorner n w d g o))) = cornerIn n w g o := by
  cases o <;> rfl

lemma frozenCorner_reverse (g : FanTriangle n w) (o : Bool) :
    (walkFrozenTarget n w d c hc f).next⁻¹ (frozenCorner n w d g (!o)) =
      walkOpposite n w d (frozenCorner n w d g o) := by
  cases o <;> rfl

variable (c hc f)
lemma walk_corner_ports (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index (P.pairing.vertex x) = frozenCorner n w d h p) :
    cornerOut n w g o = cornerIn n w h p := by
  have he : walkLabel n w d (P.index (P.pairing.edge x)) =
      rev n w (walkLabel n w d (P.index x)) := P.respects.2 x
  rw [walk_index_edge_previous n w d c hc f P hm x (by rw [hy]; rfl),hy,hx,
    frozenCorner_label] at he
  have hh := congrArg (rev n w) he
  rw [frozenCorner_previous,rev_rev] at hh
  exact hh.symm

lemma walk_corner_no_two_step (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) {x : P.Dart}
    {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index (P.pairing.vertex x) = frozenCorner n w d h p) :
    P.pairing.vertex (P.pairing.vertex x) ≠ x := by
  intro hh
  have hxy := walk_corner_ports n w d c hc f P hm hx hy
  have hyx := walk_corner_ports n w d c hc f P hm hy (by rw [hh]; exact hx)
  obtain ⟨rfl,rfl⟩ := reverse_corner_unique n w hxy hyx.symm
  apply hred x
  change P.index (P.pairing.edge x) = walkOpposite n w d (P.index x)
  rw [walk_index_edge_previous n w d c hc f P hm x (by rw [hy]; rfl),hy,hx,
    frozenCorner_reverse]

lemma walk_fan_corner {x : P.Dart} {g : FanTriangle n w} {o : Bool} {i : Fin 3}
    (hx : P.index x = .inr ⟨.inl g,o,i⟩)
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) :
    P.index x = frozenCorner n w d g o := by
  rw [hx]
  have hh := apex_side_corner n w d g o i (by rw [hx] at ha; exact ha)
  cases o <;> fin_cases i <;> first | rfl | cases hh

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
