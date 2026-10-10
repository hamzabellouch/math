import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BandScale
import OAI.Probability.CriticalPercolation.Criticality.ExhaustionEvents
import OAI.Probability.CriticalPercolation.Criticality.FiniteNearbyPair
import OAI.Probability.CriticalPercolation.Exploration.BallIncidence
import OAI.Probability.CriticalPercolation.ProductMeasure.SusceptibilityMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_clusterBand_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (z : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).clusterBand z s) =
      (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterBand z.val s} := by
  have he : (G.induce S).clusterBand z s =
      {ω | Subtype.val '' ω∈G.clusterBand z.val s} := by
    ext ω
    simp only [clusterBand,Set.mem_sdiff,G.induce_clusterTail,Set.mem_ofPred_eq]
  rw [he,G.induce_law_event S hS]

lemma induced_nearby_pair (hlocal : G.LocallyFinite) (p : unitInterval)
    (B : Finset V) (z : V) (s D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (S : Set V) (hS : S.Finite) (hB : ∀ y∈B, y∈S) (hz : z∈S) :
    (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterBand z s} *
      ((∑ y∈B, (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterTail y s}) - (s^2+D*s^3:ℕ)) ≤
        ∑ y∈B, (G.law p).real {ω | G.inducedEdges S∩ω∈G.twoClusterEvent y z s} := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  have hh := (G.induce S).finite_nearby_pair p (B.subtype (·∈S)) ⟨z,hz⟩ s D
    (G.induce_incident_bound hlocal D hD S)
  simp_rw [G.induce_clusterBand_real S (G.finite_inducedEdges hlocal hS),
    G.induce_clusterTail_real S (G.finite_inducedEdges hlocal hS),
    G.induce_twoCluster_real S (G.finite_inducedEdges hlocal hS)] at hh
  rw [Finset.sum_subtype_of_mem
    (fun y => (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterTail y s}) hB,
    Finset.sum_subtype_of_mem
    (fun y => (G.law p).real {ω | G.inducedEdges S∩ω∈G.twoClusterEvent y z s}) hB] at hh
  exact hh

lemma infinite_nearby_pair_sum [Countable E]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (p : unitInterval) (B : Finset V) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) :
    (G.law p).real (G.clusterBand z s) *
      ((∑ y∈B, (G.law p).real (G.clusterTail y s)) - (s^2+D*s^3:ℕ)) ≤
        ∑ y∈B, (G.law p).real (G.twoClusterEvent y z s) := by
  let K := G.inducedBallExhaustion hconnected hlocal z
  have hband := BernoulliProduct.tendsto_real_sdiff_finiteWitness p
    (G.clusterTail z s) (G.clusterTail z (s^2))
    (G.clusterTail_isUpperSet z s) (G.clusterTail_isUpperSet z (s^2))
    (G.clusterTail_hasFiniteOpenWitness z s) (G.clusterTail_hasFiniteOpenWitness z (s^2)) K
  have htail (y : V) := BernoulliProduct.tendsto_real_finiteWitness p
    (G.clusterTail y s) (G.clusterTail_isUpperSet y s)
    (G.clusterTail_hasFiniteOpenWitness y s) K
  have hb : Tendsto (fun n => (G.law p).real {ω | K n∩ω∈G.clusterBand z s}) atTop
      (𝓝 ((G.law p).real (G.clusterBand z s))) := by
    simpa only [law,← BernoulliProduct.law_const,clusterBand] using hband
  have ht : Tendsto (fun n => ∑ y∈B, (G.law p).real {ω | K n∩ω∈G.clusterTail y s}) atTop
      (𝓝 (∑ y∈B, (G.law p).real (G.clusterTail y s))) := by
    apply tendsto_finsetSum
    intro y _
    simpa only [law,← BernoulliProduct.law_const] using htail y
  have hh := tendsto_finsetSum B (fun y _ => G.tendsto_real_twoCluster_restrict p y z s K)
  apply le_of_tendsto_of_tendsto (hb.mul (ht.sub tendsto_const_nhds)) hh
  obtain ⟨W,hW⟩ := G.finite_subset_vertexBall hconnected z B.finite_toSet
  filter_upwards [eventually_ge_atTop W] with n hn
  exact G.induced_nearby_pair hlocal p B z s D hD _ (G.vertexBall_finite hlocal z n)
    (fun y hy => G.vertexBall_mono z hn (hW hy)) (G.mem_vertexBall_self z n)

theorem exists_nearby_large_pair [Countable E]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (p : unitInterval) (B : Finset V) (hB : B.Nonempty) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (θ : ℝ)
    (htail : ∀ y∈B, θ/2≤(G.law p).real (G.clusterTail y s))
    (hcost : (s^2+D*s^3:ℕ)≤θ/4*(B.card:ℝ)) :
    ∃ y∈B, θ/4*(G.law p).real (G.clusterBand z s) ≤
      (G.law p).real (G.twoClusterEvent y z s) := by
  have hh := G.infinite_nearby_pair_sum hconnected hlocal p B z s D hD
  have hsum : θ/4*(B.card:ℝ) ≤
      (∑ y∈B, (G.law p).real (G.clusterTail y s)) - (s^2+D*s^3:ℕ) := by
    have hs := Finset.sum_le_sum htail
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    linarith
  have hg := (mul_le_mul_of_nonneg_left hsum
    (show 0≤(G.law p).real (G.clusterBand z s) from measureReal_nonneg)).trans hh
  have hs : (∑ _y∈B, θ/4*(G.law p).real (G.clusterBand z s)) ≤
      ∑ y∈B, (G.law p).real (G.twoClusterEvent y z s) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hg
  exact Finset.exists_le_of_sum_le hB hs

end CriticalPercolation.BondGraph
end
end
end

end OAI
