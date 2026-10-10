import Mathlib
import OAI.Geometry.HyperbolicGroups.NormalCell
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.WordPictureLiteral
import OAI.Geometry.HyperbolicGroups.BoundaryIndex

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {S L V B : Type*} [DecidableEq S] [AddCommMonoid B]
namespace CellTarget
variable (T : CellTarget S L V B)

omit [DecidableEq S] in
lemma opposite_inv_next (s : S) : T.opposite (T.next⁻¹ s) = T.next (T.opposite s) := by
  have h := semiconj_perm_inv T.reverse_next s
  simpa only [inv_inv] using h

lemma reverse_boundary {xs : List S} (h : IsBoundary T.next xs) :
    IsBoundary T.next (xs.reverse.map T.opposite) := by
  have hrev : IsBoundary T.next⁻¹ xs.reverse := by
    refine ⟨by simpa using h.nodup,?_⟩
    intro x hx
    rw [List.formPerm_reverse]
    have hx' : x ∈ xs := List.mem_reverse.mp hx
    have hy : xs.formPerm⁻¹ x ∈ xs := by
      apply List.mem_of_formPerm_apply_mem
      simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hx'
    apply T.next.injective
    rw [Perm.inv_def,Equiv.apply_symm_apply,h.turn _ hy,Perm.inv_def,Equiv.apply_symm_apply]
  exact hrev.map T.opposite T.opposite.injective T.opposite_inv_next

omit [DecidableEq S] in
lemma reverse_boundary_labels {xs : List S} :
    (xs.reverse.map T.opposite).map T.edge = (xs.map (T.rev ∘ T.edge)).reverse := by
  simp only [List.map_map,List.map_reverse,Function.comp_def,T.edge_opposite]

end CellTarget
end HyperbolicObstruction.PictureSwitch

namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A S V B : Type*} [DecidableEq S] [AddCommMonoid B]
variable (T : CellTarget S (A × Bool) V B) (hinv : T.rev = invLetter)
variable {R : Set (Word A)} {w : Word A}
include hinv
namespace WordPicture
variable (P : WordPicture R w)

/-- Each relator is represented by its genuine enumerated indexed target
boundary. Coherent cellular maps are CONSTRUCTED from this attaching data;
side labels need not be injective. -/
theorem cellular_index
    (hR : ∀ r ∈ R, ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = r)
    (hw : ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = w) :
    ∃ j : P.Dart → S, IndexedFaceMap P.pairing.face T.next j ∧
      ∀ x, T.edge (j x) = P.label x := by
  apply indexedFaceMap_exists
  intro x
  by_cases hx : x ∈ P.outside
  · obtain ⟨ys,hy,hyw⟩ := hw
    exact ⟨P.outside,ys,P.boundary,hx,hy,P.word.trans hyw.symm⟩
  · obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x hx
    rcases hr with hr | hr
    · obtain ⟨ys,hys,hy⟩ := hR _ hr
      exact ⟨xs,ys,hxs,hxm,hys,hy.symm⟩
    · obtain ⟨ys,hys,hy⟩ := hR _ hr
      refine ⟨xs,ys.reverse.map T.opposite,hxs,hxm,T.reverse_boundary hys,?_⟩
      rw [T.reverse_boundary_labels,hinv]
      have he : (ys.map (invLetter ∘ T.edge)).reverse = FreeGroup.invRev (ys.map T.edge) := by
        simp only [FreeGroup.invRev,List.map_map,invLetter,Function.comp_def]
      rw [he,hy,FreeGroup.invRev_invRev]

/-- An actual mapped cellular picture, with the SAME side pairing and genus,
not a new picture-existence or normality assumption. The arbitrary exterior
must be supplied as its own target polygon, not confused with a relator. -/
theorem cellular_picture
    (hR : ∀ r ∈ R, ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = r)
    (hw : ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = w) :
    ∃ Q : CellPicture T, HEq Q.pairing P.pairing := by
  obtain ⟨j,hj,hl⟩ := P.cellular_index T hinv hR hw
  let Q : CellPicture T := {
    Dart := P.Dart
    pairing := P.pairing
    index := j
    mapped := hj
    respects := T.respects_of_edge P.pairing j hj (by
      intro x
      rw [hl,hl,hinv]
      exact P.paired x)
    genusZero := P.genusZero }
  exact ⟨Q,HEq.rfl⟩

end WordPicture

/-- Literal null words produce actual indexed target-cell pictures whenever
these are the given attaching polygons together with one exterior polygon. -/
theorem cellular_picture_existence
    (hR : ∀ r ∈ R, ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = r)
    (hw : ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = w)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    Nonempty (CellPicture.{0} T) := by
  obtain ⟨P⟩ := literal_picture_existence w h
  obtain ⟨Q,_⟩ := P.cellular_picture T hinv hR hw
  exact ⟨Q⟩

end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
