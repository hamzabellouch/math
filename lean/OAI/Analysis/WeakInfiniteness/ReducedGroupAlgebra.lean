import Mathlib
import OAI.Analysis.WeakInfiniteness.CStarClosedRange
import OAI.Analysis.WeakInfiniteness.FullGroupAlgebra
import OAI.Analysis.WeakInfiniteness.GroupRegular

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace WeakPureInfiniteness

variable {G : Type u} [Group G]

instance groupHilbertNontrivial (G : Type u) [Group G] : Nontrivial (GroupHilbert G) := by
  classical
  refine ⟨⟨0, lp.single 2 (1 : G) (1 : ℂ), ?_⟩⟩
  intro h
  have h' := congrArg (fun ξ : GroupHilbert G => ξ 1) h
  simp at h'

abbrev leftRegularRepresentation (G : Type u) [Group G] : GroupRepresentation G where
  hilbert := ⟨GroupHilbert G⟩
  group := leftRegular

def reducedGroupSubalgebra (G : Type u) [Group G] :
    StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  (fullGroupEvaluation (leftRegularRepresentation G)).range

abbrev ReducedGroupAlgebra (G : Type u) [Group G] : Type u := reducedGroupSubalgebra G

lemma reducedGroupSubalgebra_closed (G : Type u) [Group G] :
    IsClosed (reducedGroupSubalgebra G : Set (GroupHilbert G →L[ℂ] GroupHilbert G)) :=
  starHom_isClosed_range (fullGroupEvaluation (leftRegularRepresentation G))

instance (G : Type u) [Group G] : CStarAlgebra (ReducedGroupAlgebra G) := by
  letI := reducedGroupSubalgebra_closed G
  unfold ReducedGroupAlgebra
  infer_instance

def fullToReduced : FullGroupAlgebra G →⋆ₐ[ℂ] ReducedGroupAlgebra G :=
  (fullGroupEvaluation (leftRegularRepresentation G)).rangeRestrict

lemma fullToReduced_surjective : Function.Surjective (fullToReduced (G := G)) := by
  rintro ⟨x, hx⟩
  change ∃ y, fullGroupEvaluation (leftRegularRepresentation G) y = x at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

@[simp]
lemma fullToReduced_element (g : G) :
    ((fullToReduced (fullGroupElement g) : ReducedGroupAlgebra G) :
      GroupHilbert G →L[ℂ] GroupHilbert G) = leftRegular g := rfl

def fullGroupAmbientEvaluation (π : GroupRepresentation G) :
    FullGroupAmbient G →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

lemma reducedGroupSubalgebra_eq_closedStarSpan : reducedGroupSubalgebra G =
    closedStarSpan (Set.range fun g : G => (leftRegular g : GroupHilbert G →L[ℂ] GroupHilbert G)) := by
  let S := closedStarSpan (Set.range fun g : G => (leftRegular g : GroupHilbert G →L[ℂ] GroupHilbert G))
  let φ := fullGroupAmbientEvaluation (leftRegularRepresentation G)
  apply le_antisymm
  · intro x hx
    change ∃ y, fullGroupEvaluation (leftRegularRepresentation G) y = x at hx
    obtain ⟨y, rfl⟩ := hx
    have h : fullGroupSubalgebra G ≤ S.comap φ := by
      change closedStarSpan _ ≤ S.comap φ
      apply closedStarSpan_le
      · exact (closedStarSpan_closed _).preimage (starHom_continuous φ)
      · rintro _ ⟨g, rfl⟩
        exact subset_closedStarSpan _ ⟨g, rfl⟩
    exact h y.property
  · apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      change ∃ y, fullGroupEvaluation (leftRegularRepresentation G) y = _
      exact ⟨fullGroupElement g, rfl⟩
    · exact reducedGroupSubalgebra_closed G

end WeakPureInfiniteness
end

end OAI
