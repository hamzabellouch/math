import OAI.Probability.ContinuumTransition.TriangleSeparation

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def slopeGroups (P : Parameter → ℝ) (x : Parameter) (v : Fin 3 → Parameter) (τ : ℝ) (i : Fin 3) : Set Parameter :=
  subgradients pressureDomain P x ∩ closedBall (v i) τ

lemma slopeGroups_compact (P : Parameter → ℝ) (x : Parameter) (v : Fin 3 → Parameter) (τ : ℝ) (i : Fin 3) :
    IsCompact (slopeGroups P x v τ i) :=
  (isCompact_closedBall _ _).of_isClosed_subset
    ((subgradients_closed _ _ _).inter isClosed_closedBall) inter_subset_right

lemma slopeGroups_convex (P : Parameter → ℝ) (x : Parameter) (v : Fin 3 → Parameter) (τ : ℝ) (i : Fin 3) :
    Convex ℝ (slopeGroups P x v τ i) :=
  (subgradients_convex _ _ _).inter (convex_closedBall _ _)

lemma regroup_active {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P)
    (hatt : ∀ y ∈ pressureDomain, ∃ d, quadraticCost Q a y d = P y)
    {x : Parameter} (hx : x ∈ pressureDomain) {v : Fin 3 → Parameter} {τ : ℝ}
    (hA : activeLifts Q a P x ⊆ ⋃ i, closedBall (v i) τ) :
    subgradients pressureDomain P x = convexHull ℝ (⋃ i, slopeGroups P x v τ i) := by
  let K := slopeGroups P x v τ
  have hKc := compact_convexHull_iUnion_fin K (slopeGroups_compact P x v τ) (slopeGroups_convex P x v τ)
  apply Subset.antisymm
  · rw [meanField_subgradients ha hQ hP hatt hx]
    apply closedConvexHull_min _ (convex_convexHull _ _) hKc.isClosed
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hA hw)
    exact subset_convexHull ℝ _ (mem_iUnion.mpr ⟨i,activeLifts_subset hP hx hw,hi⟩)
  · apply convexHull_min _ (subgradients_convex _ _ _)
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp hw
    exact hi.1

lemma support_ball_of_vertex_groups {P : Parameter → ℝ} {x : Parameter} {p τ γ : ℝ}
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    {K : Fin 3 → Set Parameter} (hne : ∀ i, (K i).Nonempty)
    (hK : ∀ i, K i ⊆ closedBall (triangleVertex p i) τ)
    (he : subgradients pressureDomain P x = convexHull ℝ (⋃ i, K i)) :
    closedBall (triangleCenter p) γ ⊆ subgradients pressureDomain P x := by
  choose w hw using hne
  rw [he]
  exact (hgeom w (fun i => hK i (hw i))).trans (convexHull_mono (range_subset_iff.mpr fun i => mem_iUnion.mpr ⟨i,hw i⟩))

end ContinuumTemperature
end
end

end OAI
