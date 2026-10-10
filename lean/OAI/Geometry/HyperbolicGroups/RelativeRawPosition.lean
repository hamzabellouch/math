import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFacePosition
import OAI.Geometry.HyperbolicGroups.RelativeApexLocal

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

/-- The outside has no occurrence position. Its letters are genuine boundary
penalties, and cannot be silently identified with a random row field. -/
def stepPosition : WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell
    (letterDart n w ∘ word) (letterWordClosed n w ell word) → Option (RawPosition n w d)
  | .inl s => some (rawPosition n w d s)
  | .inr _ => none

variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma stepPosition_some {x : P.Dart} {p : RawPosition n w d}
    (hp : stepPosition n w d ell hell word c hc f (P.index x) = some p) :
    ∃ s, P.index x = .inl s ∧ rawPosition n w d s = p := by
  cases hi : P.index x with
  | inl s => exact ⟨s,rfl,Option.some.inj (by rw [hi] at hp; exact hp)⟩
  | inr s => rw [hi] at hp; cases hp

lemma raw_position_once_per_face (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x y : P.Dart} {p : RawPosition n w d} (hxy : P.pairing.face.SameCycle x y)
    (hx : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true)
    (hy : isLetter n w ((target n w d ell hell word c hc f).label (P.index y)) = true)
    (hpx : stepPosition n w d ell hell word c hc f (P.index x) = some p)
    (hpy : stepPosition n w d ell hell word c hc f (P.index y) = some p) : x = y := by
  obtain ⟨s,hxs,hps⟩ := stepPosition_some n w d ell hell word c hc f P hpx
  obtain ⟨t,hyt,hpt⟩ := stepPosition_some n w d ell hell word c hc f P hpy
  rw [hxs] at hx; rw [hyt] at hy
  have hcx := raw_step_cases n w d s hx
  have hcy := raw_step_cases n w d t hy
  rw [hps] at hcx; rw [hpt] at hcy
  rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy
  · exact P.normalized_index_inj hs _ hm hxy (by rw [hxs,hyt,hcx,hcy])
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy (by
      rw [hxs,hyt,hcx,hcy]; rfl))
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy.symm (by
      rw [hxs,hyt,hcx,hcy]; rfl))
  · exact P.normalized_index_inj hs _ hm hxy (by rw [hxs,hyt,hcx,hcy])

lemma contact_position_different (hred : P.FullyReduced) {x : P.Dart}
    {p : RawPosition n w d}
    (hx : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true)
    (hpx : stepPosition n w d ell hell word c hc f (P.index x) = some p)
    (hpy : stepPosition n w d ell hell word c hc f (P.index (P.pairing.edge x)) = some p) : False := by
  obtain ⟨s,hxs,hps⟩ := stepPosition_some n w d ell hell word c hc f P hpx
  obtain ⟨t,hyt,hpt⟩ := stepPosition_some n w d ell hell word c hc f P hpy
  have he := P.paired x
  rw [hxs,hyt] at he
  change walkLabel n w d t = rev n w (walkLabel n w d s) at he
  rw [hxs] at hx
  have ht : isLetter n w (walkLabel n w d t) = true := by rw [he]; exact hx
  have hp := raw_position_reverse n w d hx ht (hps.trans hpt.symm) he
  apply hred x
  rw [hxs,hyt,hp]
  rfl

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
