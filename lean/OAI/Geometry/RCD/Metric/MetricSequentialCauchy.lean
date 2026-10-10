import Mathlib.Topology.MetricSpace.Cauchy

namespace OAI

/-! # A Cauchy criterion along pairs of diverging index sequences -/

open Filter
open scoped Topology
namespace RegularPointCoordinates

theorem cauchySeq_of_pairwise_tendsto {E : Type*} [PseudoMetricSpace E] (F : ℕ → E)
    (h : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun k => dist (F (i k)) (F (j k))) atTop (𝓝 0)) : CauchySeq F := by
  rw [Metric.cauchySeq_iff]
  by_contra hc
  push Not at hc
  obtain ⟨ε,hε,hbad⟩ := hc
  choose i hi j hj hdist using hbad
  have hit : Tendsto i atTop atTop := tendsto_atTop_mono hi tendsto_id
  have hjt : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  have he : ε ≤ 0 := ge_of_tendsto (h i j hit hjt) (Eventually.of_forall hdist)
  exact (not_le_of_gt hε) he

end RegularPointCoordinates

end OAI
