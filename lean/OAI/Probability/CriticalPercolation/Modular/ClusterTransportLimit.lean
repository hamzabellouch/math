import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterMassRestriction
import OAI.Probability.CriticalPercolation.Modular.ClusterTransportFinite

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma transport_sum_out_le (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) :
    (∑' e, transport G r s p ω u e) ≤ rootAbsolute G s p ω u := by
  rw [transport_sum_out]
  split_ifs
  · exact (le_abs_self _).trans_eq (abs_rootDiscrepancy G s p ω u)
  · exact rootAbsolute_nonneg G s p ω u

omit [Countable V] [Countable E] in
lemma transport_sum_out_abs (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) :
    |∑' e, transport G r s p ω u e| ≤ rootAbsolute G s p ω u := by
  rw [transport_sum_out]
  split_ifs
  · exact (abs_rootDiscrepancy G s p ω u).le
  · exact (abs_zero).le.trans (rootAbsolute_nonneg G s p ω u)

lemma integrable_transport_out (hl : G.LocallyFinite) (D : ℕ)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (r s : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (u : V) :
    Integrable (fun ω => ∑' e, transport G r s p ω u e) (G.law p) := by
  apply Integrable.mono' (integrable_const ((D:ℝ)/(p:ℝ)))
    (Measurable.tsum (fun e => measurable_transport G r s p u e)).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => (transport_sum_out_abs G r s p ω u).trans
    (rootAbsolute_bound G hl D hD s hp ω u))

lemma expectedTransport_out_bound (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (r k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) (u : V) :
    (∑' e, expectedTransport G r (4^k) p u e) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  rw [expectedTransport_sum_out G hl r (4^k) p hp u]
  refine (integral_mono_ae (integrable_transport_out G hl D hD r (4^k) p hp u) ?_
    (Eventually.of_forall (fun ω => transport_sum_out_le G r (4^k) p ω u))).trans
    (subcritical_rootAbsolute_bound G hl D hDpos hD p hp hpc k u)
  apply Integrable.mono' (integrable_const ((D:ℝ)/(p:ℝ)))
    (measurable_rootAbsolute G (4^k) p u).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rootAbsolute_nonneg G (4^k) p ω u)]
    exact rootAbsolute_bound G hl D hD (4^k) hp ω u)

omit [Countable V] [Countable E] in
lemma eventually_truncatedEdgeMass (hc : G.fullGraph.Connected) {ω : Set E} {e : E}
    (hx : (G.cluster ω (G.ends e).out.1).Finite)
    (hy : (G.cluster ω (G.ends e).out.2).Finite) (s : ℕ) :
    ∀ᶠ r in atTop, truncatedEdgeMass G r s ω e = edgeMass G s ω e := by
  filter_upwards [eventually_small G hc hx,eventually_small G hc hy] with r hr hs
  simp only [truncatedEdgeMass,clusterWeight,hr,hs,ite_true,edgeMass]

lemma expectedTransport_in_tendsto (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (s : ℕ) (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) (e : E) :
    Tendsto (fun r => ∑' u, expectedTransport G r s p u e) atTop
      (𝓝 (∫ ω, edgeDiscrepancy G s p ω e ∂G.law p)) := by
  simp only [expectedTransport_sum_in G hl _ s p hp e]
  apply tendsto_integral_of_dominated_convergence (fun _ => 2/(p:ℝ))
  · intro r
    exact (Measurable.tsum (fun u => measurable_transport G r s p u e)).aestronglyMeasurable
  · exact integrable_const _
  · intro r
    exact Eventually.of_forall (fun ω => transport_sum_in_bound G hl r s hp ω e)
  · filter_upwards [ae_finite_clusters G p hpc] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_truncatedEdgeMass G hc (hω _) (hω _) s] with r hr
    rw [transport_sum_in G hl,hr]
    rfl

end CriticalPercolation.FiniteClusters
end
end

end OAI
