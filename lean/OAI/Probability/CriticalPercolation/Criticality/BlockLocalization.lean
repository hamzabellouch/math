import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf
import OAI.Probability.CriticalPercolation.Clusters.ClusterObject
import OAI.Probability.CriticalPercolation.Criticality.NestedLayerBlock
import OAI.Probability.CriticalPercolation.Criticality.OpenRay
import OAI.Probability.CriticalPercolation.Exploration.SliceExploration
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finset_weight_lower (o : V) (C : Set V) (F : Finset V) (hF : (F : Set V)⊆C)
    (r : ℝ≥0∞) (hr : ∀ x∈F, r≤G.stabilizerWeight o x) :
    r*F.card≤G.modularMass o C := by
  calc
    r*F.card = ∑ _x∈F, r := by simp [nsmul_eq_mul,mul_comm]
    _ ≤ ∑ x∈F, if x∈C then G.stabilizerWeight o x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [ite_eq_left (hF hx)]
      exact hr x hx
    _ ≤ _ := ENNReal.sum_le_tsum F

lemma cluster_subset_ball_of_mass
    (S : Set V) (v : V) (hv : v∈S) (ω : Set E) (r : ℝ≥0∞)
    (hr : ∀ x∈S, r≤G.stabilizerWeight v x) (M : ℝ≥0∞) (B : ℕ)
    (hB : M<r*(B+1)) (hm : G.modularMass v (G.cluster (ω∩G.inducedEdges S) v)≤M) :
    G.cluster (ω∩G.inducedEdges S) v⊆G.vertexBall v B := by
  intro x hx
  obtain ⟨w⟩ := hx
  let p := w.toPath
  have hF : (p.val.support.toFinset : Set V)⊆G.cluster (ω∩G.inducedEdges S) v := by
    intro y hy
    exact ⟨p.val.takeUntil y (List.mem_toFinset.mp hy)⟩
  have hmass := G.finset_weight_lower v _ p.val.support.toFinset hF r
    (fun y hy => hr y (G.cluster_induced_subset ω S hv (hF hy)))
  have hcard : p.val.support.toFinset.card=p.val.length+1 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,p.val.length_support]
  rw [hcard,Nat.cast_add,Nat.cast_one] at hmass
  have hlen : p.val.length≤B := by
    by_contra hn
    have hnat : B+1≤p.val.length+1 := by omega
    have hle : r*(B+1)≤r*(p.val.length+1) := by
      gcongr
      exact_mod_cast (show B≤p.val.length by omega)
    exact (not_le_of_gt hB) (hle.trans (hmass.trans hm))
  have hh := G.openWalk_getVert_ball p.val p.val.length le_rfl
  rw [SimpleGraph.Walk.getVert_length] at hh
  exact G.vertexBall_mono v hlen hh

lemma cluster_eq_of_incident_agree (v : V) (ω η : Set E)
    (h : ∀ e∈G.incidentEdges (G.cluster ω v), e∈ω ↔ e∈η) :
    G.cluster η v=G.cluster ω v := by
  have hh := G.roots_eq_of_incident (S := {v}) (U := G.cluster ω v)
    (ω := ω) (ω' := η)
    (by simp only [ClusterDeletion.roots_singleton,ClusterDeletion.component,cluster]) h
  simpa only [ClusterDeletion.roots_singleton,ClusterDeletion.component,cluster] using hh

lemma freshClusterBoundary_subset_incident (X : Set E) (v : V) (ω : Set E) :
    G.freshClusterBoundary X v ω⊆G.incidentEdges (G.cluster (ω∩X) v) := by
  rintro e ⟨⟨x,y,he,_,hy⟩,_⟩
  exact ⟨y,hy,by rw [he]; simp⟩

lemma boundedDomainFreshExit_of_agree
    (D S : Set V) (v : V) (hv : v∈S) (r M : ℝ≥0∞) (B N : ℕ)
    (hr : ∀ x∈S, r≤G.stabilizerWeight v x) (hB : M<r*(B+1))
    (ω η : Set E)
    (hagree : ∀ e∈G.incidentEdges (G.vertexBall v B), e∈ω ↔ e∈η)
    (hω : ω∈G.boundedDomainFreshExitEvent D S v N M) :
    η∈G.boundedDomainFreshExitEvent D S v N M := by
  have hball := G.cluster_subset_ball_of_mass S v hv (ω∩G.inducedEdges D) r hr M B hB hω.2
  have hinc := G.incidentEdges_mono hball
  have heq : G.cluster ((η∩G.inducedEdges D)∩G.inducedEdges S) v =
      G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges S) v := by
    apply G.cluster_eq_of_incident_agree
    intro e he
    simp only [Set.mem_inter_iff,hagree e (hinc he)]
  refine ⟨?_,?_⟩
  swap
  · change G.modularMass v (G.cluster ((η∩G.inducedEdges D)∩G.inducedEdges S) v)≤M
    rw [heq]
    exact hω.2
  obtain ⟨F,hF,hFω⟩ := hω.1
  refine ⟨F,hF,fun e he => ?_⟩
  have hfresh := (hFω he).1
  have hei := G.freshClusterBoundary_subset_incident (G.inducedEdges S) v
    (ω∩G.inducedEdges D) hfresh
  refine ⟨?_,(hagree e (hinc hei)).mp (hFω he).2.1,(hFω he).2.2⟩
  simpa only [freshClusterBoundary,heq] using hfresh

lemma dependsOn_boundedDomainFreshExit
    (D S : Set V) (v : V) (hv : v∈S) (r M : ℝ≥0∞) (B N : ℕ)
    (hr : ∀ x∈S, r≤G.stabilizerWeight v x) (hB : M<r*(B+1)) :
    DependsOn (fun ω : Set E => ω∈G.boundedDomainFreshExitEvent D S v N M)
      (G.incidentEdges (G.vertexBall v B)) := by
  intro ω η h
  apply propext
  exact ⟨G.boundedDomainFreshExit_of_agree D S v hv r M B N hr hB ω η
    (fun e he => (h e he).to_iff),
    G.boundedDomainFreshExit_of_agree D S v hv r M B N hr hB η ω
    (fun e he => (h e he).symm.to_iff)⟩

end CriticalPercolation.BondGraph
end
end

end OAI
