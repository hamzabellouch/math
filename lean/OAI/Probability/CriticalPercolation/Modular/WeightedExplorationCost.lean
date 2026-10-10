import Mathlib
import OAI.Probability.CriticalPercolation.Modular.ClusterMassRestriction
import OAI.Probability.CriticalPercolation.Modular.WeightedIncidenceSearch
import OAI.Probability.CriticalPercolation.Modular.ModularIncidence
import OAI.Probability.CriticalPercolation.Modular.PeakClusters

namespace OAI

section
noncomputable section
open Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma bondWeight_le_of_clusterPeak (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hp : G.clusterPeak ω x) {e : E} (he : e∈G.incidentEdges (G.cluster ω x)) :
    G.bondWeight x e ≤ (2*K : ℕ) := by
  obtain ⟨v,hv,hve⟩ := he
  exact (G.bondWeight_le_at_end hc hl K hK x v e hve).trans
    (by simpa only [mul_one] using mul_le_mul_right (hp v hv) (2*K : ℕ))

lemma restriction_incident_subset (s : Set E) (ω : Set E) (x : V) {e : s}
    (he : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x)) :
    e.val∈G.incidentEdges (G.cluster ω x) := by
  obtain ⟨v,hv,hve⟩ := he
  refine ⟨v,?_,hve⟩
  rw [FiniteClusters.restrict_cluster] at hv
  exact G.cluster_mono Set.inter_subset_right x hv

lemma restriction_weighted_quadratic_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (s : Set E) [Fintype s]
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x) :
    ENNReal.ofReal ((IncidenceSearch.tree (G.restrictEdges s) x).quadraticCost
      (fun e : s => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω)) ≤
      (D*(2*K)^2 : ℕ)*G.modularMass x (G.cluster ω x) := by
  rw [IncidenceSearch.tree_quadratic,ENNReal.ofReal_sum_of_nonneg
    (fun e _ => by split_ifs <;> positivity)]
  have hsum : (∑ e : s, if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x) := by
    calc
      _ ≤ ∑ e : s, if e.val∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e.val else 0 := by
        apply Finset.sum_le_sum
        intro e _
        split_ifs with he he'
        · rfl
        · exact False.elim (he' (G.restriction_incident_subset s ω x he))
        · exact zero_le
        · rfl
      _ ≤ ∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0 := by
        change (∑ e : s, (fun e : E => if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0) e.val) ≤ _
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comp_le_tsum_of_injective (f := (Subtype.val : s → E)) Subtype.val_injective
            (fun e : E => if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0))
      _ ≤ _ := G.weighted_incidence_le hc hl D K hD hK x _
  calc
    _ ≤ ∑ e : s, (2*K : ℕ)*(if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (G.bondWeight_ne_top x e.val),pow_two]
        exact mul_le_mul_left (G.bondWeight_le_of_clusterPeak hc hl K hK ω x hp
          (G.restriction_incident_subset s ω x he)) _
      · simp
    _ = (2*K : ℕ)*(∑ e : s, if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2*K : ℕ)*((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)) := mul_le_mul_right hsum _
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow]; ring

lemma restriction_quadratic_real_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (s : Set E) [Fintype s]
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (U : ℝ) (hU : 0≤U) (hm : G.modularMass x (G.cluster ω x)≤ENNReal.ofReal U) :
    (IncidenceSearch.tree (G.restrictEdges s) x).quadraticCost
      (fun e : s => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω) ≤ (D*(2*K)^2 : ℕ)*U := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc _ ≤ (D*(2*K)^2 : ℕ)*G.modularMass x (G.cluster ω x) :=
        G.restriction_weighted_quadratic_le hc hl D K hD hK s ω x hp
       _ ≤ (D*(2*K)^2 : ℕ)*ENNReal.ofReal U := mul_le_mul_right hm _
       _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

end CriticalPercolation.BondGraph
end
end

end OAI
