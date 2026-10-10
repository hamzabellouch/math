import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Tactic

namespace OAI

/-! # A sequential criterion for a Cauchy sequence -/
noncomputable section
open Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

theorem cauchySeq_of_pairwise_subsequences {X : Type*} [PseudoEMetricSpace X] (u : ℕ → X)
    (h : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun n => edist (u (i n)) (u (j n))) atTop (𝓝 0)) : CauchySeq u := by
  classical
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_contra hn
  push Not at hn
  choose i hi j hj hd using hn
  have hit : Tendsto i atTop atTop := tendsto_atTop_mono hi tendsto_id
  have hjt : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  obtain ⟨n,hsmall⟩ := ((h i j hit hjt).eventually (gt_mem_nhds hε)).exists
  exact not_lt_of_ge (hd n) hsmall

end BoltzmannNonuniqueness.Compactness

end

end OAI
