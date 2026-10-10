import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFanIncoming

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

lemma frozenCorner_start (g : FanTriangle n w) (o : Bool) :
    start n w (walkLabel n w d (frozenCorner n w d g o)) = .inr g.1 := by
  rw [frozenCorner_label]
  cases o <;> rfl

/-- The same indexed fan field occurs at most once at one normalized apex
instance, INCLUDING opposite triangle orientations. Opposite orientations
would force a canceling two-step vertex link. -/
lemma fan_field_once (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))
    {x y : P.Dart} {g : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index y = frozenCorner n w d g p)
    (hxy : P.pairing.vertex.SameCycle x y) : x = y := by
  have hax : isApex n w (start n w (walkLabel n w d (P.index x))) = true := by
    rw [hx,frozenCorner_start]; rfl
  by_cases hop : o = p
  · apply hrad x y hax hxy
    change walkLabel n w d (P.index x) = walkLabel n w d (P.index y)
    rw [hx,hy,hop]
  · have hprev : ∀ z : P.Dart, P.pairing.vertex.SameCycle (P.pairing.vertex⁻¹ z) z :=
      fun z => sameCycle_inv.mp (SameCycle.rfl (x := z)).apply_left
    have hp : p = !o := by cases o <;> cases p <;> simp_all
    have h1 : P.pairing.vertex⁻¹ x = y := by
      refine hrad _ _ ?_ ((hprev x).trans hxy) ?_
      · change isApex n w (start n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)))) = true
        rw [walk_start_link_constant n w d c hc f P (hprev x)]
        exact hax
      · change walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)) = walkLabel n w d (P.index y)
        rw [walk_corner_incoming n w d c hc f P hm hx,hy,frozenCorner_label,hp]
        cases o <;> rfl
    have h2 : P.pairing.vertex⁻¹ y = x := by
      refine hrad _ _ ?_ ((hprev y).trans hxy.symm) ?_
      · change isApex n w (start n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ y)))) = true
        rw [walk_start_link_constant n w d c hc f P ((hprev y).trans hxy.symm)]
        exact hax
      · change walkLabel n w d (P.index (P.pairing.vertex⁻¹ y)) = walkLabel n w d (P.index x)
        rw [walk_corner_incoming n w d c hc f P hm hy,hx,frozenCorner_label,hp]
        cases o <;> rfl
    exact False.elim (walk_triangle_inverse_no_two n w d c hc f P hm hred hx
      (by rw [h1]; exact hy) (by rw [h1,h2]))

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
