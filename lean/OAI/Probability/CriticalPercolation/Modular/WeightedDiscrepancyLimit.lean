import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterMassRestriction
import OAI.Probability.CriticalPercolation.Modular.WeightedDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.WeightedIncidenceSearch

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def restrictedWeightedTerm (s : Set E) (p : ℝ) (ω : Set E) (x : V) (e : E) : ℝ :=
  if e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x) then
    (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0

def restrictedWeightedDiscrepancy (s : Set E) (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  ∑' e, G.restrictedWeightedTerm s p ω x e

lemma restrictedWeightedDiscrepancy_eq_tree (s : Set E) [Fintype s]
    (p : ℝ) (ω : Set E) (x : V) :
    G.restrictedWeightedDiscrepancy s p ω x =
      (IncidenceSearch.tree (G.restrictEdges s) x).weightedSum
        (fun e : s => (G.bondWeight x e.val).toReal) p (Subtype.val ⁻¹' ω) := by
  rw [IncidenceSearch.tree_weighted]
  unfold restrictedWeightedDiscrepancy restrictedWeightedTerm
  have ht : (∑' e : E, if e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x) then
      (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0) =
      ∑' e : s, if e.val∈G.incidentEdges (G.cluster (s∩ω) x) then
        (G.bondWeight x e.val).toReal*centeredCoefficient p ω e.val else 0 := by
    rw [tsum_subtype s (fun e : E => if e∈G.incidentEdges (G.cluster (s∩ω) x) then
      (G.bondWeight x e).toReal*centeredCoefficient p ω e else 0)]
    apply tsum_congr
    intro e
    by_cases he : e∈s <;> simp only [Set.indicator,he,ite_true,ite_false,true_and,false_and]
  rw [ht,tsum_fintype]
  apply Finset.sum_congr rfl
  intro e _
  have hi : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) ↔
      e.val∈G.incidentEdges (G.cluster (s∩ω) x) := by
    rw [FiniteClusters.restrict_cluster]
    rfl
  rw [hi]
  unfold centeredCoefficient
  simp only [Set.mem_preimage]
  split_ifs <;> ring

lemma norm_restrictedWeightedTerm_le (s : Set E) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (e : E) :
    ‖G.restrictedWeightedTerm s p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold restrictedWeightedTerm
  by_cases he : e∈s ∧ e∈G.incidentEdges (G.cluster (s∩ω) x)
  · have hi : e∈G.incidentEdges (G.cluster ω x) := by
      obtain ⟨v,hv,hve⟩ := he.2
      exact ⟨v,G.cluster_mono Set.inter_subset_right x hv,hve⟩
    rw [ite_eq_left he,ite_eq_left hi,Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · rw [ite_eq_right he,norm_zero]
    exact ENNReal.toReal_nonneg

lemma eventually_restrictedWeightedTerm (K : Set.FiniteExhaustion (Set.univ : Set E))
    (p : ℝ) (ω : Set E) (x : V) (e : E) :
    ∀ᶠ n in atTop, G.restrictedWeightedTerm (K n) p ω x e=G.weightedIncidenceTerm p ω x e := by
  by_cases he : e∈G.incidentEdges (G.cluster ω x)
  · obtain ⟨v,hv,hve⟩ := he
    obtain ⟨s,hs,hsω,hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n,hn⟩ := finite_subset_exhaustion K (hs.insert e) (Set.subset_univ _)
    apply eventually_atTop.mpr
    refine ⟨n,fun m hm => ?_⟩
    have heK : e∈K m := K.mono hm (hn (Set.mem_insert e s))
    have hsK : s⊆K m := fun a ha => K.mono hm (hn (Set.mem_insert_of_mem e ha))
    have hem : e∈G.incidentEdges (G.cluster (K m∩ω) x) :=
      ⟨v,G.cluster_mono (Set.subset_inter hsK hsω) x hvs,hve⟩
    have hefull : e∈G.incidentEdges (G.cluster ω x) := ⟨v,hv,hve⟩
    simp only [restrictedWeightedTerm,weightedIncidenceTerm,heK,hem,hefull,true_and,ite_true]
  · apply Eventually.of_forall
    intro n
    have hen : ¬(e∈K n ∧ e∈G.incidentEdges (G.cluster (K n∩ω) x)) := by
      rintro ⟨_,v,hv,hve⟩
      exact he ⟨v,G.cluster_mono Set.inter_subset_right x hv,hve⟩
    simp only [restrictedWeightedTerm,weightedIncidenceTerm,ite_eq_right hen,ite_eq_right he]

theorem tendsto_restrictedWeightedDiscrepancy (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (L : Set.FiniteExhaustion (Set.univ : Set E)) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.restrictedWeightedDiscrepancy (L n) p ω x) atTop
      (𝓝 (G.weightedDiscrepancy p ω x)) := by
  apply tendsto_tsum_of_dominated_convergence
    (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm)
  · intro e
    apply tendsto_const_nhds.congr'
    filter_upwards [G.eventually_restrictedWeightedTerm L p ω x e] with n hn
    exact hn.symm
  · exact Eventually.of_forall (fun n e => G.norm_restrictedWeightedTerm_le (L n) p hp ω x e)

end CriticalPercolation.BondGraph
end
end

end OAI
