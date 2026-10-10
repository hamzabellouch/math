import Mathlib
import OAI.Geometry.HyperbolicGroups.NormalCell
import OAI.Geometry.HyperbolicGroups.WordPicture
import OAI.Geometry.HyperbolicGroups.WordPictureCell
import OAI.Geometry.HyperbolicGroups.BoundaryIndex

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A S V B K : Type*} [DecidableEq S] [AddCommMonoid B]
variable (T : CellTarget S (A × Bool) V B) (hinv : T.rev = invLetter)
variable {R : Set (Word A)} {w : Word A}
include hinv
namespace WordPicture
variable (P : WordPicture R w)

/-- Coherent indexing retains a distinguished face tag. In particular the
outside can only map to the positive exterior polygon; no opposite exterior
face or extra exterior face is silently introduced. -/
theorem cellular_index_tag (tag : S → K) (inside outside : K)
    (hR : ∀ r ∈ R, ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = r ∧
      (∀ y ∈ ys, tag y = inside ∧ tag (T.opposite y) = inside))
    (hw : ∃ ys : List S, IsBoundary T.next ys ∧ ys.map T.edge = w ∧
      (∀ y ∈ ys, tag y = outside)) :
    ∃ j : P.Dart → S, IndexedFaceMap P.pairing.face T.next j ∧
      (∀ x, T.edge (j x) = P.label x) ∧
      ∀ x, tag (j x) = if x ∈ P.outside then outside else inside := by
  let lab : P.Dart → K × (A × Bool) :=
    fun x => (if x ∈ P.outside then outside else inside, P.label x)
  let edge : S → K × (A × Bool) := fun s => (tag s,T.edge s)
  have hex : ∀ x : P.Dart, ∃ xs : List P.Dart, ∃ ys : List S,
      IsBoundary P.pairing.face xs ∧ x ∈ xs ∧ IsBoundary T.next ys ∧
        xs.map lab = ys.map edge := by
    intro x
    by_cases hx : x ∈ P.outside
    · obtain ⟨ys,hy,hyw,hyt⟩ := hw
      refine ⟨P.outside,ys,P.boundary,hx,hy,?_⟩
      have he1 : P.outside.map lab = P.outside.map (fun x => (outside,P.label x)) := by
        apply List.map_congr_left
        intro z hz
        simp only [lab,ite_eq_left hz]
      have he2 : ys.map edge = ys.map (fun y => (outside,T.edge y)) := by
        apply List.map_congr_left
        intro z hz
        simp only [edge,hyt z hz]
      rw [he1,he2]
      change P.outside.map ((fun l => (outside,l)) ∘ P.label) =
        ys.map ((fun l => (outside,l)) ∘ T.edge)
      rw [← List.map_map,← List.map_map,P.word,hyw]
    · obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x hx
      have hout : ∀ z ∈ xs, z ∉ P.outside := by
        intro z hz hzo
        exact hx (P.boundary.mem_of_sameCycle hzo (hxs.sameCycle hz hxm))
      have he1 : xs.map lab = xs.map (fun x => (inside,P.label x)) := by
        apply List.map_congr_left
        intro z hz
        simp only [lab,ite_eq_right (hout z hz)]
      have present : ∀ ys : List S, IsBoundary T.next ys →
          ys.map T.edge = xs.map P.label → (∀ y ∈ ys, tag y = inside) →
          ∃ xs' ys', IsBoundary P.pairing.face xs' ∧ x ∈ xs' ∧ IsBoundary T.next ys' ∧
            xs'.map lab = ys'.map edge := by
        intro ys hys he htag
        refine ⟨xs,ys,hxs,hxm,hys,?_⟩
        have he2 : ys.map edge = ys.map (fun y => (inside,T.edge y)) := by
          apply List.map_congr_left
          intro z hz
          simp only [edge,htag z hz]
        rw [he1,he2]
        change xs.map ((fun l => (inside,l)) ∘ P.label) =
          ys.map ((fun l => (inside,l)) ∘ T.edge)
        rw [← List.map_map,← List.map_map,he]
      rcases hr with hr | hr
      · obtain ⟨ys,hys,hy,ht⟩ := hR _ hr
        exact present ys hys hy (fun y hy => (ht y hy).1)
      · obtain ⟨ys,hys,hy,ht⟩ := hR _ hr
        apply present (ys.reverse.map T.opposite) (T.reverse_boundary hys)
        · rw [T.reverse_boundary_labels,hinv]
          have he : (ys.map (invLetter ∘ T.edge)).reverse = FreeGroup.invRev (ys.map T.edge) := by
            simp only [FreeGroup.invRev,List.map_map,invLetter,Function.comp_def]
          rw [he,hy,FreeGroup.invRev_invRev]
        · intro y hy
          obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hy
          exact (ht z (List.mem_reverse.mp hz)).2
  obtain ⟨j,hj,hl⟩ := indexedFaceMap_exists _ _ lab edge hex
  exact ⟨j,hj,(fun x => congrArg Prod.snd (hl x)),(fun x => congrArg Prod.fst (hl x))⟩

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
