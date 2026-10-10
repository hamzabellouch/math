import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFrozenTarget
import OAI.Geometry.HyperbolicGroups.WalkRawPosition

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.WalkPicture
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma free_sameface_not_opposite (hs : P.Simple) (hb : P.NoBigon)
    {x y : P.Dart} (hx : T.free (T.kind (P.index x)) = true)
    (hxy : P.pairing.face.SameCycle x y) : P.index y ≠ T.opposite (P.index x) := by
  intro hop
  have hy : T.free (T.kind (P.index y)) = true := by rw [hop,T.opposite_kind]; exact hx
  have h1 : P.pairing.face x = y := by
    apply P.simple_front hs (P.free_face hx) hxy.apply_left
    rw [hop,T.opposite_front]
    exact P.closed x
  have h2 : P.pairing.face y = x := by
    apply P.simple_front hs (P.free_face hy) hxy.symm.apply_left
    calc
      _ = T.back (P.index y) := P.closed y
      _ = _ := by rw [hop,T.opposite_back]
  exact hb x hx (by rw [h1,h2])

lemma frozen_sameface_not_opposite (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x y : P.Dart} (hx : T.free (T.kind (P.index x)) = false)
    (hxy : P.pairing.face.SameCycle x y) : P.index y ≠ T.opposite (P.index x) := by
  intro hop
  let x' : P.FrozenDart := ⟨x,hx⟩
  let y' : P.FrozenDart := ⟨y,P.opposite_frozen hx hop⟩
  have hh : P.frozenFace.SameCycle x' y' := hxy.subtypePerm
  have ht := semiconj_perm_sameCycle hm.commute hh
  change B.next.SameCycle (P.index x) (P.index y) at ht
  rw [hop,← B.reverse_eq] at ht
  exact B.opposite_cycle _ ht

lemma normalized_index_inj (hs : P.Simple) (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x y : P.Dart} (hxy : P.pairing.face.SameCycle x y)
    (he : P.index x = P.index y) : x = y := by
  cases hf : T.free (T.kind (P.index x)) with
  | true => exact P.simple_front hs hf hxy (congrArg T.front he)
  | false =>
    let x' : P.FrozenDart := ⟨x,hf⟩
    let y' : P.FrozenDart := ⟨y,by rw [← he]; exact hf⟩
    have hh : P.frozenFace.SameCycle x' y' := hxy.subtypePerm
    have h := hm.injective hh (show P.index x = P.index y from he)
    exact congrArg Subtype.val h

lemma normalized_sameface_not_opposite (hs : P.Simple) (hb : P.NoBigon)
    (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x y : P.Dart} (hxy : P.pairing.face.SameCycle x y) :
    P.index y ≠ T.opposite (P.index x) := by
  cases hf : T.free (T.kind (P.index x)) with
  | true => exact P.free_sameface_not_opposite hs hb hf hxy
  | false => exact P.frozen_sameface_not_opposite B hm hf hxy
end HyperbolicObstruction.PictureSwitch.WalkPicture

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- Every individual source face uses each indexed letter position at most
once. For a top this uses simplicity AND absence of two-step polygons. -/
lemma raw_position_once_per_face (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x y : P.Dart} (hxy : P.pairing.face.SameCycle x y)
    (hx : isLetter n w (walkLabel n w d (P.index x)) = true)
    (hy : isLetter n w (walkLabel n w d (P.index y)) = true)
    (hp : rawPosition n w d (P.index x) = rawPosition n w d (P.index y)) : x = y := by
  have hcx := raw_step_cases n w d (P.index x) hx
  have hcy := raw_step_cases n w d (P.index y) hy
  rw [← hp] at hcy
  rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy
  · exact P.normalized_index_inj hs _ hm hxy (hcx.trans hcy.symm)
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy (by
      change P.index y = walkOpposite n w d (P.index x)
      rw [hcx,hcy]))
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy.symm (by
      change P.index x = walkOpposite n w d (P.index y)
      rw [hcx,hcy]))
  · exact P.normalized_index_inj hs _ hm hxy (hcx.trans hcy.symm)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
