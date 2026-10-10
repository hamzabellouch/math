import OAI.Probability.ContinuumTransition.Persistence

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

structure HasVertexTriple (P : Parameter → ℝ) (x : Parameter) (p b : ℝ) : Prop where
  center : SupportOn pressureDomain P x (triangleCenter p)
  hull : subgradients pressureDomain P x = convexHull ℝ (⋃ i, slopeGroups P x (triangleVertex p) b i)

lemma HasVertexTriple.support_ball {P : Parameter → ℝ} {x : Parameter} {p b τ γ : ℝ}
    (h : HasVertexTriple P x p b) (hp : 0 < p) (hb : b ≤ τ) (hτ : τ ≤ p/100)
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w)) :
    closedBall (triangleCenter p) γ ⊆ subgradients pressureDomain P x := by
  have hK (i : Fin 3) : slopeGroups P x (triangleVertex p) b i ⊆ closedBall (triangleVertex p i) τ :=
    inter_subset_right.trans (closedBall_subset_closedBall hb)
  exact support_ball_of_vertex_groups hgeom
    (all_vertex_groups_nonempty hp hτ _ hK (h.hull ▸ h.center)) hK h.hull

lemma HasVertexTriple.separated {P : Parameter → ℝ} {x : Parameter} {p b : ℝ}
    (hp : 0 < p) (hb : b ≤ p/100) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (Prod.snd '' slopeGroups P x (triangleVertex p) b i)
      (Prod.snd '' slopeGroups P x (triangleVertex p) b j) :=
  (vertex_density_separation hp hb hij).mono (image_mono inter_subset_right) (image_mono inter_subset_right)

end ContinuumTemperature
end
end

end OAI
