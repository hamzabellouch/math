import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeMappedWalk
import OAI.Geometry.HyperbolicGroups.WalkFanCorner
import OAI.Geometry.HyperbolicGroups.MacroRadialIndex

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

lemma walk_apex_cases (x : P.Dart)
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) :
    (∃ a e, P.index x = .inl (a,e)) ∨ ∃ g o, P.index x = frozenCorner n w d g o := by
  cases hx : P.index x with
  | inl s => exact Or.inl ⟨s.1,s.2,rfl⟩
  | inr s =>
    rcases s with ⟨g,o,i⟩
    rcases g with g | (s | z)
    · exact Or.inr ⟨g,o,by
        have h := walk_fan_corner n w d c hc f P hx ha
        rw [hx] at h
        exact h⟩
    · exfalso
      change Fin 4 at i
      rw [hx] at ha
      cases o with
      | false =>
        change isApex n w (start n w (rev n w (squareSide n w s i))) = true at ha
        rw [squareSide_end] at ha
        cases ha
      | true =>
        change isApex n w (start n w (squareSide n w s i)) = true at ha
        rw [squareSide_start] at ha
        cases ha
    · exfalso
      change Fin 6 at i
      rw [hx] at ha
      cases o with
      | false =>
        change isApex n w (start n w (rev n w (letterDart n w (z.val i)))) = true at ha
        rw [rev_letter,start_letter] at ha
        cases ha
      | true =>
        change isApex n w (start n w (letterDart n w (z.val i))) = true at ha
        rw [start_letter] at ha
        cases ha

/-- Consecutive top turns in one normalized apex link cannot belong to the
same top occurrence, even when their simple macro polygons are different. -/
lemma walk_top_adjacent_different (hred : P.FullyReduced) {x : P.Dart}
    {a b : Top n w} {e k : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (a,e)) (hy : P.index (P.pairing.vertex x) = .inl (b,k))
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) : a ≠ b := by
  intro hab; subst b
  obtain ⟨j,hj⟩ := same_top_face n w d c hc f P hy
    ((SameCycle.rfl (f := P.pairing.face) (x := P.pairing.edge x)).apply_left)
  have hpair := P.paired x
  change walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) at hpair
  rw [hj,hx] at hpair
  change macroStep n w a j.adj = rev n w (macroStep n w a e.adj) at hpair
  have hj' : macroStep n w a j.symm.adj = macroStep n w a e.adj := by
    exact (macroStep_reverse n w a j.adj).trans
      ((congrArg (rev n w) hpair).trans (rev_rev n w _))
  have he : e = j.symm := macroStep_radial_injective n w a e j.symm
    (by rw [hx] at ha; exact ha) hj'.symm
  have hje : j = e.symm := by rw [he]; rfl
  apply hred x
  rw [hj,hx,hje]
  rfl

/-- Two turns of one simple source top face over the same ACTUAL fan are
identical. The argument retains the indexed fan type even if numerical
letters and row fields repeat. -/
lemma walk_top_unique_turn (hs : P.Simple) {x y : P.Dart} {a : Top n w}
    {e : MacroGraph.graph.Dart} (hx : P.index x = .inl (a,e))
    (hxy : P.pairing.face.SameCycle x y) (b : Fan n w)
    (hax : start n w (walkLabel n w d (P.index x)) = .inr b)
    (hay : start n w (walkLabel n w d (P.index y)) = .inr b) : x = y := by
  obtain ⟨k,hk⟩ := same_top_face n w d c hc f P hx hxy
  rw [hx] at hax
  rw [hk] at hay
  change start n w (macroStep n w a e.adj) = .inr b at hax
  change start n w (macroStep n w a k.adj) = .inr b at hay
  have hax := (macroStep_start n w a e.adj).symm.trans hax
  have hay := (macroStep_start n w a k.adj).symm.trans hay
  have he : e.fst = k.fst := (macroVertex_at_apex n w a e.fst b hax).trans
    (macroVertex_at_apex n w a k.fst b hay).symm
  apply P.simple_front hs (by rw [hx]; rfl) hxy
  change walkFront n w d (P.index x) = walkFront n w d (P.index y)
  rw [hx,hk]
  exact congrArg Sum.inl (Prod.ext rfl he)

lemma walk_apex_no_fixed (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (x : P.Dart)
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) :
    P.pairing.vertex x ≠ x := by
  intro he
  rcases walk_apex_cases n w d c hc f P x ha with ⟨a,e,hx⟩ | ⟨g,o,hx⟩
  · exact walk_top_adjacent_different n w d c hc f P hred hx (by rw [he]; exact hx) ha rfl
  · have hports := walk_corner_ports n w d c hc f P hm hx (by rw [he]; exact hx)
    exact corner_bipartite n w g o (congrArg (dartPart n w) hports)

lemma walk_link_card (hrad : P.RadialInjective (isApex n w)) (a : P.Dart) (b : Fan n w)
    (ha : start n w (walkLabel n w d (P.index a)) = .inr b) :
    Fintype.card {x : P.Dart // P.pairing.vertex.SameCycle a x} ≤ 5 := by
  let j : {x : P.Dart // P.pairing.vertex.SameCycle a x} → Outgoing n w b := fun x =>
    ⟨walkLabel n w d (P.index x.val),
      (walk_start_link_constant n w d c hc f P x.property).symm.trans ha⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hrad x.val y.val
    · change isApex n w (start n w (walkLabel n w d (P.index x.val))) = true
      rw [← walk_start_link_constant n w d c hc f P x.property,ha]; rfl
    · exact x.property.symm.trans y.property
    · exact congrArg Subtype.val hxy
  exact (Fintype.card_le_of_injective j hj).trans (card_outgoing n w b)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
