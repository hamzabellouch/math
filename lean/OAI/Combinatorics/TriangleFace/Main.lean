import OAI.Combinatorics.TriangleFace.Faces
import OAI.Combinatorics.TriangleFace.MatchingImage

namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem local_face {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) :
    let H := triangleExpansion G c v
    let f := localExtension G c v hc
    let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
    f '' G.polytope = Q ∧
    Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
    (∀ x, oldRestriction (f x) = x) ∧
    (∀ y ∈ Q, f (oldRestriction y) = y) ∧
    (∀ x e, f x (Sum.inl e) = x e) ∧
    (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
    (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
    (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x) := by
  dsimp only
  have him := expansion_image_eq G c v hc
  have hex := expansion_image_extreme G c v hc
  refine ⟨him, ?_, ?_, restriction_extension G c v hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← him]
    exact (convex_convexHull ℝ (Set.range G.indicator)).linear_image (localExtension G c v hc)
  · rwa [← him]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := him.symm ▸ hy
    rfl
  · intro x e
    rfl
  · intro x i
    rfl
  · intro x hx e
    rcases e with e | i
    · exact hx e
    · exact hx (localEdge G c v hc i)
  · intro x hx
    exact (CanonicalFace198.image_minFace
      (localExtension G c v hc).toAffineMap (localExtension_injective G c v hc)
      (convex_convexHull ℝ (Set.range G.indicator))
      (convex_convexHull ℝ (Set.range (triangleExpansion G c v).indicator)) hex hx).symm

theorem triangle_expansion_face {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3)
    (_hmatching : Nonempty G.Matching) :
    ∃ (c : E → Fin 3) (hc : LocalLabels G v c),
      let H := triangleExpansion G c v
      let f := localExtension G c v hc
      let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
      f '' G.polytope = Q ∧
      Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
      (∀ x, oldRestriction (f x) = x) ∧
      (∀ y ∈ Q, f (oldRestriction y) = y) ∧
      (∀ x e, f x (Sum.inl e) = x e) ∧
      (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
      (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
      (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x) := by
  obtain ⟨c,hc⟩ := labels_of_degree_three G v hdeg
  exact ⟨c,hc,local_face G c v hc⟩

end TriangleFace198
end

end OAI
