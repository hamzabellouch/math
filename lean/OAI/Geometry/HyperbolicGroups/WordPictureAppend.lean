import Mathlib
import OAI.Geometry.HyperbolicGroups.FaceSplice
import OAI.Geometry.HyperbolicGroups.BoundarySplice
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.PictureSum

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace IsBoundary
variable {D : Type*} [DecidableEq D] {f : Perm D} {xs ys : List D}
lemma splice_nonempty (hx : IsBoundary f xs) (hy : IsBoundary f ys)
    (hxn : xs ≠ []) (hyn : ys ≠ []) (hd : ∀ x ∈ xs, x ∉ ys) :
    IsBoundary (f * swap (xs.getLast hxn) (ys.getLast hyn)) (xs++ys) := by
  obtain ⟨b,r,rfl⟩ := List.exists_cons_of_ne_nil hyn
  have h := splice_append (l := xs.dropLast) (a := xs.getLast hxn)
    (by simpa only [List.dropLast_append_getLast] using hx) hy
    (by simpa only [List.dropLast_append_getLast] using hd)
  simpa only [List.dropLast_append_getLast] using h
lemma splice_away (hx : IsBoundary f xs) {a b : D} (ha : a ∉ xs) (hb : b ∉ xs) :
    IsBoundary (f * swap a b) xs := by
  refine ⟨hx.nodup,?_⟩
  intro x hm
  have hxa : x ≠ a := fun h => ha (h ▸ hm)
  have hxb : x ≠ b := fun h => hb (h ▸ hm)
  rw [mul_apply,swap_apply_of_ne_of_ne hxa hxb]
  exact hx.turn x hm
end IsBoundary
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {u v : Word A}
namespace WordPicture
variable (P : WordPicture R u) (Q : WordPicture R v)

/-- Literal concatenation by a genus-zero connected sum at exterior corners. -/
def appendNonempty (hp : P.outside ≠ []) (hq : Q.outside ≠ []) : WordPicture R (u++v) where
  Dart := P.Dart ⊕ Q.Dart
  pairing := (P.pairing.sum Q.pairing).splice
    (Sum.inl (P.outside.getLast hp)) (Sum.inr (Q.outside.getLast hq))
  genusZero := (P.pairing.sum Q.pairing).splice_genusZero
    (P.pairing.sum_genusZero Q.pairing P.genusZero Q.genusZero) _ _
    (P.pairing.sum_not_components Q.pairing _ _)
  label := Sum.elim P.label Q.label
  paired := by
    intro x; cases x with
    | inl x => exact P.paired x
    | inr x => exact Q.paired x
  outside := P.outside.map Sum.inl ++ Q.outside.map Sum.inr
  boundary := by
    have hp' : P.outside.map (Sum.inl (β := Q.Dart)) ≠ [] := by simpa using hp
    have hq' : Q.outside.map (Sum.inr (α := P.Dart)) ≠ [] := by simpa using hq
    have h := IsBoundary.splice_nonempty
      (P.boundary.map (g := (P.pairing.sum Q.pairing).face) (Sum.inl (β := Q.Dart)) Sum.inl_injective (fun _ => rfl))
      (Q.boundary.map (g := (P.pairing.sum Q.pairing).face) (Sum.inr (α := P.Dart)) Sum.inr_injective (fun _ => rfl))
      hp' hq' (by simp only [List.mem_map]; rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩; cases he)
    simpa only [List.getLast_map,PictureMap.splice] using h
  word := by simp only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr,P.word,Q.word]
  interior := by
    intro z hz
    cases z with
    | inl x =>
      have hx : x ∉ P.outside := by intro hx; exact hz (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
      obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x hx
      have hdis : ∀ a ∈ xs, a ∉ P.outside := by
        intro a ha hoa
        exact hx (P.boundary.mem_of_sameCycle hoa (hxs.sameCycle ha hxm))
      refine ⟨xs.map Sum.inl,?_,List.mem_map.mpr ⟨x,hxm,rfl⟩,?_⟩
      · exact (hxs.map (Sum.inl (β := Q.Dart)) Sum.inl_injective (fun _ => rfl)).splice_away
          (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩; exact hdis y hy (Sum.inl.inj he ▸ List.getLast_mem hp))
          (by simp)
      · simpa only [List.map_map,Function.comp_def,Sum.elim_inl] using hr
    | inr x =>
      have hx : x ∉ Q.outside := by intro hx; exact hz (List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
      obtain ⟨xs,hxs,hxm,hr⟩ := Q.interior x hx
      have hdis : ∀ a ∈ xs, a ∉ Q.outside := by
        intro a ha hoa
        exact hx (Q.boundary.mem_of_sameCycle hoa (hxs.sameCycle ha hxm))
      refine ⟨xs.map Sum.inr,?_,List.mem_map.mpr ⟨x,hxm,rfl⟩,?_⟩
      · exact (hxs.map (Sum.inr (α := P.Dart)) Sum.inr_injective (fun _ => rfl)).splice_away
          (by simp)
          (by simp only [List.mem_map]; rintro ⟨y,hy,he⟩; exact hdis y hy (Sum.inr.inj he ▸ List.getLast_mem hq))
      · simpa only [List.map_map,Function.comp_def,Sum.elim_inr] using hr

def append : WordPicture R (u++v) := by
  by_cases hp : P.outside = []
  · have hu : u = [] := by rw [← P.word,hp]; rfl
    simpa only [hu,List.nil_append] using Q
  by_cases hq : Q.outside = []
  · have hv : v = [] := by rw [← Q.word,hq]; rfl
    simpa only [hv,List.append_nil] using P
  exact P.appendNonempty Q hp hq
end WordPicture
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
