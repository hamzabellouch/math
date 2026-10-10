import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFanCapacity
import OAI.Geometry.HyperbolicGroups.RelativeApexLocal

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma frozenCorner_start (g : FanTriangle n w) (o : Bool) :
    start n w ((target n w d ell hell word c hc f).label (.inl (frozenCorner n w d g o))) = .inr g.1 := by
  rw [corner_label]
  cases o <;> rfl

/-- The same indexed fan field occurs at most once at one normalized apex
instance, INCLUDING opposite triangle orientations. Opposite orientations
would force a canceling two-step vertex link. -/
lemma fan_field_once (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))
    {x y : P.Dart} {g : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index y = .inl (frozenCorner n w d g p))
    (hxy : P.pairing.vertex.SameCycle x y) : x = y := by
  have hax : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true := by
    rw [hx,frozenCorner_start]; rfl
  by_cases hop : o = p
  · apply hrad x y hax hxy
    rw [hx,hy,hop]
  · have hprev : ∀ z : P.Dart, P.pairing.vertex.SameCycle (P.pairing.vertex⁻¹ z) z :=
      fun z => sameCycle_inv.mp (SameCycle.rfl (x := z)).apply_left
    have hp : p = !o := by cases o <;> cases p <;> simp_all
    have h1 : P.pairing.vertex⁻¹ x = y := by
      refine hrad _ _ ?_ ((hprev x).trans hxy) ?_
      · change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)))) = true
        rw [start_link_constant n w d ell hell word c hc f P (hprev x)]
        exact hax
      · rw [corner_incoming n w d ell hell word c hc f P hm hx,hy,corner_label,hp]
        cases o <;> rfl
    have h2 : P.pairing.vertex⁻¹ y = x := by
      refine hrad _ _ ?_ ((hprev y).trans hxy.symm) ?_
      · change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ y)))) = true
        rw [start_link_constant n w d ell hell word c hc f P ((hprev y).trans hxy.symm)]
        exact hax
      · rw [corner_incoming n w d ell hell word c hc f P hm hy,hx,corner_label,hp]
        cases o <;> rfl
    exact False.elim (triangle_inverse_no_two n w d ell hell word c hc f P hm hred hx
      (by rw [h1]; exact hy) (by rw [h1,h2]))

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
