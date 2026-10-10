import Mathlib
import OAI.Probability.CriticalPercolation.Modular.WeightedDiscrepancy
import OAI.Probability.CriticalPercolation.Clusters.ClusterCountFlip
import OAI.Probability.CriticalPercolation.ProductMeasure.BernoulliSingletonIntegration
import OAI.Probability.CriticalPercolation.Criticality.SignedCountIdentity

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def clusterCountDrop (ω : Set E) (e : E) : ℝ :=
  (G.incidentClusterCount (ω\{e}) e).toReal -
    (G.incidentClusterCount (insert e ω) e).toReal

lemma clusterCountDrop_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.clusterCountDrop ω e =
      if ¬(G.openGraph (ω\{e})).Reachable a b ∧
        ¬(G.modularMass a (G.cluster (ω\{e}) a)=∞ ∧
          G.modularMass b (G.cluster (ω\{e}) b)=∞) then 1 else 0 := by
  have hi : insert e (ω\{e})=insert e ω := by ext f; by_cases h : f=e <;> simp [h]
  simpa only [clusterCountDrop,hi] using G.incidentClusterCount_flip_of_ends hc hl (ω\{e}) e a b he

lemma clusterCountDrop_mem (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : G.clusterCountDrop ω e=0 ∨ G.clusterCountDrop ω e=1 := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.clusterCountDrop_of_ends hc hl ω e a b he.symm]
  split_ifs <;> simp

lemma measurable_clusterCountDrop [Countable V] [Countable E] (e : E) :
    Measurable (fun ω => G.clusterCountDrop ω e) := by
  unfold clusterCountDrop
  exact ((G.measurable_incidentClusterCount e).comp
    (by have h := BernoulliProduct.measurable_forceOn ({e}:Set E) ∅
        change Measurable (fun ω => BernoulliProduct.forceOn {e} ∅ ω) at h
        simpa only [forceOn_empty_singleton] using h)).ennreal_toReal.sub
    ((G.measurable_incidentClusterCount e).comp
    (by have h := BernoulliProduct.measurable_forceOn ({e}:Set E) Set.univ
        change Measurable (fun ω => BernoulliProduct.forceOn {e} Set.univ ω) at h
        simpa only [forceOn_univ_singleton] using h)).ennreal_toReal

lemma integral_centered_incidentClusterCount [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval) (e : E) :
    (∫ ω, centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal ∂G.law p) =
      -(p:ℝ)*(1-(p:ℝ))*(∫ ω, G.clusterCountDrop ω e ∂G.law p) := by
  have h := BernoulliProduct.integral_centered_singleton (fun _ : E => p) e
    (fun ω => (G.incidentClusterCount ω e).toReal)
    (G.measurable_incidentClusterCount e).ennreal_toReal 2 (by norm_num) (fun ω => by
      simpa only [Function.comp_apply,Real.norm_of_nonneg ENNReal.toReal_nonneg] using
        G.incidentClusterCount_toReal_le_two hc hl ω e)
  rw [BernoulliProduct.law_const, ←show G.law p=ProbabilityTheory.setBernoulli Set.univ p from rfl] at h
  change (∫ ω, (if e∈ω then 1-(p:ℝ) else -(p:ℝ))*(G.incidentClusterCount ω e).toReal ∂G.law p) = _
  rw [h]
  simp only [forceOn_empty_singleton,forceOn_univ_singleton]
  have hi (σ : Set E) : Integrable (fun ω => (G.incidentClusterCount
      (BernoulliProduct.forceOn {e} σ ω) e).toReal) (G.law p) := by
    apply Integrable.of_bound ((G.measurable_incidentClusterCount e).ennreal_toReal.comp
      (BernoulliProduct.measurable_forceOn _ _)).aestronglyMeasurable 2
    exact Eventually.of_forall (fun ω => by
      simpa only [Function.comp_apply,Real.norm_of_nonneg ENNReal.toReal_nonneg] using
        G.incidentClusterCount_toReal_le_two hc hl _ e)
  have hio := hi Set.univ
  have hic := hi ∅
  simp only [forceOn_empty_singleton,forceOn_univ_singleton] at hio hic
  rw [show (∫ ω, G.clusterCountDrop ω e ∂G.law p) =
      (∫ ω, (G.incidentClusterCount (ω\{e}) e).toReal ∂G.law p)-
      (∫ ω, (G.incidentClusterCount (insert e ω) e).toReal ∂G.law p) from integral_sub hic hio]
  ring

theorem expected_signed_discrepancy_drop [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)=
      -(p:ℝ)*(1-(p:ℝ))*(∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
        ∫ ω, G.clusterCountDrop ω e ∂G.law p) := by
  rw [G.expected_signed_discrepancy_count hc hl hq D K hD hK]
  simp_rw [G.integral_centered_incidentClusterCount hc hl,Finset.mul_sum]

end CriticalPercolation.BondGraph
end
end

end OAI
