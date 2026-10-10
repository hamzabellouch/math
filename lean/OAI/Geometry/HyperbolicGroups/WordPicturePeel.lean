import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.EdgeEraseBoundary
import OAI.Geometry.HyperbolicGroups.EdgeEraseGenus

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]
namespace PictureMap
variable (M : PictureMap D) {a : D} {xs : List D}

lemma eraseEdge_other_boundary (h : IsBoundary M.face xs)
    (ha : a ∉ xs) (hb : M.edge a ∉ xs) :
    IsBoundary (M.eraseEdge a).face
      (xs.attachWith (OffPair a (M.edge a))
        (fun _ hx => ⟨fun he => ha (he ▸ hx), fun he => hb (he ▸ hx)⟩)) := by
  apply h.lift
  intro x hx
  have hxa : x ≠ a := fun he => ha (he ▸ hx)
  have hxb : x ≠ M.edge a := fun he => hb (he ▸ hx)
  have hfa : M.face x ≠ a := fun he => ha (he ▸ h.invariant hx)
  have hfb : M.face x ≠ M.edge a := fun he => hb (he ▸ h.invariant hx)
  change bypassPair (M.face*swap a (M.edge a)) a (M.edge a) x = M.face x
  rw [bypassPair,bypass_away _ _ _ hxb,bypass_away _ _ _ hxa]
  simp only [mul_apply,swap_apply_of_ne_of_ne hxa hxb,ite_eq_right hfa,ite_eq_right hfb]

end PictureMap
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
variable (P : WordPicture R w)

/-- Peeling a genuine interior face adjacent to the outside deletes one
paired edge and retains every other indexed relator boundary and label. -/
def peelAt {a : P.Dart} {l r : List P.Dart} (he : P.outside = a::l)
    (hr : IsBoundary P.pairing.face (P.pairing.edge a::r))
    (hne : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    WordPicture R ((r++l).map P.label) := by
  have hl : IsBoundary P.pairing.face (a::l) := he ▸ P.boundary
  have hs := hl.splice_heads hr (hl.disjoint hr (by simp) (by simp) hne)
  have hp := IsBoundary.splice_heads_offpair hs.nodup
  let M := P.pairing.eraseEdge a
  refine {
    Dart := {x // OffPair a (P.pairing.edge a) x}
    pairing := M
    genusZero := P.pairing.eraseEdge_genusZero a P.genusZero hne
    label := P.label ∘ Subtype.val
    paired := fun x => P.paired x.val
    outside := (r++l).attachWith (OffPair a (P.pairing.edge a)) hp
    boundary := ?_
    word := List.attachWith_map_val hp
    interior := ?_ }
  · apply hs.erase_head.erase_at.lift hp
    intro x hx
    rfl
  · intro x hx
    have hxrl : x.val ∉ r++l := fun h => hx ((List.mem_attachWith hp x).mpr h)
    have hxo : x.val ∉ P.outside := by
      rw [he]
      intro hm
      rcases List.mem_cons.mp hm with h | h
      · exact x.property.1 h
      · exact hxrl (List.mem_append_right _ h)
    have hxi : x.val ∉ P.pairing.edge a::r := by
      intro hm
      rcases List.mem_cons.mp hm with h | h
      · exact x.property.2 h
      · exact hxrl (List.mem_append_left _ h)
    obtain ⟨xs,hxs,hxm,hrel⟩ := P.interior x.val hxo
    have ha : a ∉ xs := by
      intro ha
      exact hxo (P.boundary.mem_of_sameCycle (by rw [he]; simp) (hxs.sameCycle ha hxm))
    have hb : P.pairing.edge a ∉ xs := by
      intro hb
      exact hxi (hr.mem_of_sameCycle (by simp) (hxs.sameCycle hb hxm))
    have hp' : ∀ y ∈ xs, OffPair a (P.pairing.edge a) y :=
      fun y hy => ⟨fun he => ha (he ▸ hy),fun he => hb (he ▸ hy)⟩
    refine ⟨xs.attachWith _ hp',P.pairing.eraseEdge_other_boundary hxs ha hb,
      (List.mem_attachWith hp' x).mpr hxm,?_⟩
    simpa only [Function.comp_def,List.attachWith_map_val] using hrel

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
