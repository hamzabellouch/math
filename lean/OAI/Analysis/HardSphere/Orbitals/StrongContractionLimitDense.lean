import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
lemma strong_contraction_limit_of_dense {E F ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {l : Filter ι} (A : ι → E →L[ℂ] E) (B : E →L[ℂ] E)
    (hA : ∀ t u, ‖A t u‖≤‖u‖) (hB : ∀ u, ‖B u‖≤‖u‖)
    (f : F → E) (hf : DenseRange f)
    (ht : ∀ y, Tendsto (fun t ↦ A t (f y)) l (𝓝 (B (f y)))) (u : E) :
    Tendsto (fun t ↦ A t u) l (𝓝 (B u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y,hy⟩ := hf.exists_dist_lt u (show 0<ε/3 by positivity)
  filter_upwards [(Metric.tendsto_nhds.mp (ht y)) (ε/3) (by positivity)] with t ht
  have h1 : dist (A t u) (A t (f y))≤dist u (f y) := by
    simpa only [dist_eq_norm,map_sub] using hA t (u-f y)
  have h2 : dist (B (f y)) (B u)≤dist (f y) u := by
    simpa only [dist_eq_norm,map_sub] using hB (f y-u)
  have htriangle := dist_triangle4 (A t u) (A t (f y)) (B (f y)) (B u)
  rw [dist_comm (f y) u] at h2
  linarith
end HardSphere

end

end OAI
