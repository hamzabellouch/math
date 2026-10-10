import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkCell
import OAI.Geometry.HyperbolicGroups.BoundaryList
import OAI.Geometry.HyperbolicGroups.ProtectedNormal

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

/-- A literal boundary can be pulled back through an injective survival map,
provided every one of its sides survives and its successor is retained. -/
lemma IsBoundary.pullback_surviving {D E : Type*} [DecidableEq D] [DecidableEq E]
    {p : Perm D} {q : Perm E} {xs : List D} (h : IsBoundary p xs)
    (j : E → D) (hj : Function.Injective j)
    (hcomplete : ∀ x ∈ xs, ∃ y, j y = x)
    (hface : ∀ y, j y ∈ xs → j (q y) = p (j y)) :
    ∃ ys : List E, IsBoundary q ys ∧ ys.map j = xs := by
  let k : {x : D // x ∈ xs} → E := fun x => Classical.choose (hcomplete x.val x.property)
  have hk : ∀ x, j (k x) = x.val := fun x => Classical.choose_spec (hcomplete x.val x.property)
  let ys := xs.attach.map k
  have he : ys.map j = xs := by
    dsimp only [ys]
    rw [List.map_map]
    have hc : j ∘ k = Subtype.val := funext hk
    rw [hc,List.attach_map_subtype_val]
  refine ⟨ys,⟨?_,?_⟩,he⟩
  · exact List.Nodup.of_map j (he ▸ h.nodup)
  · intro y hy
    have hx : j y ∈ xs := he ▸ List.mem_map_of_mem hy
    apply hj
    rw [hface y hx,h.turn _ hx,← he,formPerm_map_apply j hj]

namespace WalkPicture
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A] {T : WalkCellTarget S C W L V A}
  {P Q : WalkPicture.{u} T} {keep : S → Prop}

/-- Protected-boundary normalization retains the EXACT enumerated word, not
merely its conjugacy class or its image in the presented group. -/
theorem Preserves.boundary (hPQ : P.Preserves keep Q)
    (hk : ∀ s, keep s → T.free (T.kind s) = false)
    (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
    (hs : ∀ x, keep (P.index x) ↔ x ∈ xs) :
    ∃ ys : List Q.Dart, IsBoundary Q.pairing.face ys ∧
      ys.map hPQ.map = xs ∧
      ys.map (T.label ∘ Q.index) = xs.map (T.label ∘ P.index) ∧
      ∀ y, keep (Q.index y) ↔ y ∈ ys := by
  obtain ⟨ys,hy,he⟩ := hx.pullback_surviving hPQ.map hPQ.injective
    (fun x hx => hPQ.complete x ((hs x).mpr hx)) (by
      intro y hy
      apply hPQ.face
      rw [hPQ.index]
      exact hk _ ((hs _).mpr hy))
  refine ⟨ys,hy,he,?_,?_⟩
  · rw [← he,List.map_map]
    apply List.map_congr_left
    intro y _
    exact congrArg T.label (hPQ.index y)
  · intro y
    rw [hPQ.index,hs,← he]
    exact List.mem_map_of_injective hPQ.injective

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
