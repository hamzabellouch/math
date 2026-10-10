import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterMassEndpoint
import OAI.Probability.CriticalPercolation.Modular.ClusterTransportLimit
import OAI.Probability.CriticalPercolation.Modular.Unimodularity

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteClusters

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma incident_tsum_eq (hl : G.LocallyFinite) (v : V) (f : E → ℝ) :
    (∑' e, if v ∈ G.ends e then G.bondShare e * f e else 0) =
      ∑ e ∈ (hl v).toFinset, G.bondShare e * f e := by
  rw [tsum_eq_sum (f := fun e => if v ∈ G.ends e then G.bondShare e * f e else 0)
    (s := (hl v).toFinset) (fun e he => ite_eq_right (fun h => he ((hl v).mem_toFinset.mpr h)))]
  apply Finset.sum_congr rfl
  intro e he
  exact ite_eq_left (show v ∈ G.ends e from (hl v).mem_toFinset.mp he)

lemma UnimodularRoot.truncated_average_bound (R : G.UnimodularRoot)
    (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (r k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) :
    (∑ v ∈ R.roots, R.weight v * ∑ e ∈ (hl v).toFinset, G.bondShare e *
      ∑' u, expectedTransport G r (4^k) p u e) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  have hb := UnimodularRoot.bond_balance G R hl (expectedTransport G r (4^k) p)
    (fun φ u e => expectedTransport_aut G φ r (4^k) p u e)
    (expectedTransport_row_finite G hl r (4^k) p)
    (expectedTransport_column_finite G hl r (4^k) p)
  simp only [G.incident_tsum_eq hl] at hb
  rw [← hb]
  calc
    _ ≤ ∑ u ∈ R.roots, R.weight u * ((D:ℝ)/p*(6/(2:ℝ)^k)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (expectedTransport_out_bound G hl D hDpos hD r k p hp hpc u)
        (R.positive u hu).le
    _ = _ := by rw [← Finset.sum_mul,R.normalized,one_mul]

lemma UnimodularRoot.average_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) :
    (∑ v ∈ R.roots, R.weight v * ∑ e ∈ (hl v).toFinset, G.bondShare e *
      ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω e ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  apply le_of_tendsto (x := atTop) (f := fun r => ∑ v ∈ R.roots, R.weight v *
    ∑ e ∈ (hl v).toFinset, G.bondShare e * ∑' u, expectedTransport G r (4^k) p u e) ?_
    (Eventually.of_forall (fun r => UnimodularRoot.truncated_average_bound G R hl D hDpos hD r k p hp hpc))
  apply tendsto_finsetSum
  intro v hv
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro e he
  exact (expectedTransport_in_tendsto G hc hl (4^k) p hp hpc e).const_mul _

lemma UnimodularRoot.incident_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability)
    {v : V} (hv : v ∈ R.roots) {e : E} (he : v ∈ G.ends e) :
    R.weight v * G.bondShare e * (G.law p).real
        (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
      (D:ℝ)/p*(6/(2:ℝ)^k) := by
  have hle (f : E) := subcritical_endpoint_le_integral G hl (4^k) (by positivity) p hp hpc f
  have hn (f : E) : 0 ≤ ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p := measureReal_nonneg.trans (hle f)
  calc
    _ ≤ R.weight v * (G.bondShare e * ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω e ∂G.law p) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle e) (G.bondShare_pos e).le)
        (R.positive v hv).le
    _ ≤ R.weight v * ∑ f ∈ (hl v).toFinset, G.bondShare f *
        ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p := by
      apply mul_le_mul_of_nonneg_left _ (R.positive v hv).le
      exact Finset.single_le_sum (fun f _ => mul_nonneg (G.bondShare_pos f).le (hn f))
        ((hl v).mem_toFinset.mpr he)
    _ ≤ ∑ u ∈ R.roots, R.weight u * ∑ f ∈ (hl u).toFinset, G.bondShare f *
        ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p := by
      exact Finset.single_le_sum (f := fun u => R.weight u * ∑ f ∈ (hl u).toFinset,
        G.bondShare f * ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p)
        (fun u hu => mul_nonneg (R.positive u hu).le
        (Finset.sum_nonneg (fun f _ => mul_nonneg (G.bondShare_pos f).le (hn f)))) hv
    _ ≤ _ := UnimodularRoot.average_bound G R hc hl D hDpos hD k p hp hpc

end CriticalPercolation.BondGraph
end
end

end OAI
