import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryEraseList
import OAI.Geometry.HyperbolicGroups.BoundaryIndex
import OAI.Geometry.HyperbolicGroups.IndexedWordPicture
import OAI.Geometry.HyperbolicGroups.PolygonBoundaryList
import OAI.Geometry.HyperbolicGroups.WordPictureCell

namespace OAI

/-! Literal nullword disks with chosen persistent cell identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}

lemma outsideInvariant (P : WordPicture R w) (x : P.Dart) :
    P.pairing.face x ∈ P.outside ↔ x ∈ P.outside :=
  ⟨fun h => P.boundary.mem_of_sameCycle h SameCycle.rfl.apply_left,
    fun h => P.boundary.mem_of_sameCycle h SameCycle.rfl.apply_right⟩

abbrev InsideDart (P : WordPicture R w) := {x : P.Dart // x ∉ P.outside}
def insideFace (P : WordPicture R w) : Perm P.InsideDart :=
  P.pairing.face.subtypePerm (fun x => not_congr (P.outsideInvariant x))

variable {B : PolygonTarget.Boundary C (E × Bool) V} (P : WordPicture R w)

/-- Convert a coherent map on the genuine interior faces into a persistent
optional index on the entire diagram. -/
def Indexing.ofInterior (j : P.InsideDart → B.Side)
    (hj : IndexedFaceMap P.insideFace B.next j)
    (hl : ∀ x, P.label x.val = B.sideLabel (j x)) : Indexing B P where
  index x := if hx : x ∈ P.outside then none else some (j ⟨x,hx⟩)
  outside x := by by_cases hx : x ∈ P.outside <;> simp [hx]
  commute x := by
    by_cases hx : x ∈ P.outside
    · simp [hx,(P.outsideInvariant x).mpr hx]
    · have hf : P.pairing.face x ∉ P.outside := fun h => hx ((P.outsideInvariant x).mp h)
      simp only [dite_eq_right hx,dite_eq_right hf,Option.map_some]
      exact congrArg some (hj.commute ⟨x,hx⟩)
  injective := by
    intro x y hxy s hx hy
    by_cases hxo : x ∈ P.outside
    · simp [hxo] at hx
    by_cases hyo : y ∈ P.outside
    · simp [hyo] at hy
    simp only [dite_eq_right hxo,dite_eq_right hyo,Option.some.injEq] at hx hy
    exact congrArg Subtype.val (hj.injective (sameCycle_subtypePerm.mpr hxy) (hx.trans hy.symm))
  label x s hx := by
    by_cases hxo : x ∈ P.outside
    · simp [hxo] at hx
    simp only [dite_eq_right hxo,Option.some.injEq] at hx
    exact (hl ⟨x,hxo⟩).trans (congrArg B.sideLabel hx)

variable (B)
lemma indexing_exists (hrev : B.rev = invLetter)
    (P : WordPicture (Set.range B.attachingWord) w) : Nonempty (Indexing B P) := by
  let T := B.target (fun _ => (0 : ℤ)) (fun _ => false) (by intro l h; cases h)
  have hex : ∀ x : P.InsideDart, ∃ xs : List P.InsideDart, ∃ ys : List B.Side,
      IsBoundary P.insideFace xs ∧ x ∈ xs ∧ IsBoundary B.next ys ∧
        xs.map (P.label ∘ Subtype.val) = ys.map B.sideLabel := by
    intro x
    obtain ⟨xs,hs,hxm,hr⟩ := P.interior x.val x.property
    have hdis : ∀ a ∈ xs, a ∉ P.outside := by
      intro a ha hoa
      exact x.property (P.boundary.mem_of_sameCycle hoa (hs.sameCycle ha hxm))
    have hb : IsBoundary P.insideFace (xs.attachWith (fun a => a ∉ P.outside) hdis) :=
      hs.lift hdis P.insideFace (fun _ _ => rfl)
    have hm : x ∈ xs.attachWith (fun a => a ∉ P.outside) hdis :=
      (List.mem_attachWith hdis x).mpr hxm
    rcases hr with ⟨c,hc⟩ | ⟨c,hc⟩
    · refine ⟨_,B.positiveSides c,hb,hm,B.positiveSides_boundary c,?_⟩
      simpa only [Function.comp_def,List.attachWith_map_val,B.positiveSides_label] using hc.symm
    · refine ⟨_,(B.positiveSides c).reverse.map B.opposite,hb,hm,T.reverse_boundary (B.positiveSides_boundary c),?_⟩
      have hh := T.reverse_boundary_labels (xs := B.positiveSides c)
      change ((B.positiveSides c).reverse.map B.opposite).map B.sideLabel =
        ((B.positiveSides c).map (B.rev ∘ B.sideLabel)).reverse at hh
      rw [hh,hrev]
      have he : ((B.positiveSides c).map (invLetter ∘ B.sideLabel)).reverse =
          FreeGroup.invRev (B.attachingWord c) := by
        rw [← List.map_map,B.positiveSides_label]
        rfl
      rw [he,hc,FreeGroup.invRev_invRev]
      exact List.attachWith_map_val hdis
  obtain ⟨j,hj,hl⟩ := indexedFaceMap_exists P.insideFace B.next
    (P.label ∘ Subtype.val) B.sideLabel hex
  exact ⟨Indexing.ofInterior P j hj (fun x => (hl x).symm)⟩

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
