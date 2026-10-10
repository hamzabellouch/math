import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure
import OAI.Probability.CriticalPercolation.Criticality.FiniteEdgeInterpolation

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma restrictEdges_twoClusterEvent (S : Set E) (u v : V) (s : ℕ) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set S)) ⁻¹'
      ((G.restrictEdges S).twoClusterEvent u v s) =
        {ω | S ∩ ω ∈ G.twoClusterEvent u v s} := by
  ext ω
  simp only [Set.mem_preimage,twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    clusterTail,cluster,G.restrictEdges_openGraph]

lemma real_law_domRestrict (p : unitInterval) (S : Set E) (hS : S.Finite)
    (A : Set (Set S)) :
    ((G.restrictEdges S).law p).real A =
      (G.law p).real ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set S)) ⁻¹' A) := by
  let := hS.fintype
  have hr := BernoulliProduct.law_map_restrict (fun _ : E => p) S
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set S)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [BernoulliProduct.law_const] at hr
  change (setBernoulli (Set.univ : Set S) p).real A = _
  rw [← hr,Measure.real,Measure.map_apply hmeas (.of_discrete)]
  rfl

lemma restrictEdges_twoCluster_real (p : unitInterval) (S : Set E) (hS : S.Finite)
    (u v : V) (s : ℕ) :
    ((G.restrictEdges S).law p).real ((G.restrictEdges S).twoClusterEvent u v s) =
      (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent u v s} := by
  rw [G.real_law_domRestrict p S hS,G.restrictEdges_twoClusterEvent]

lemma restrictEdges_reachable_real (p : unitInterval) (S : Set E) (hS : S.Finite) (u v : V) :
    ((G.restrictEdges S).law p).real {ω | ((G.restrictEdges S).openGraph ω).Reachable u v} =
      (G.law p).real {ω | (G.openGraph (S ∩ ω)).Reachable u v} := by
  rw [G.real_law_domRestrict p S hS]
  congr 1
  ext ω
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.restrictEdges_openGraph]

theorem restricted_interpolation_measure (S : Set E) (hS : S.Finite)
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0<c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph (S ∩ ω)).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s}) :
    ∃ j<d, 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s} ∧
      -Real.log ((G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s}) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s})+Nat.clog 2 d+1) := by
  let := hS.fintype
  have h := (G.restrictEdges S).finite_edge_interpolation_measure d x hd p hp hc hε hεp hεq
  simp_rw [G.restrictEdges_twoCluster_real p S hS,G.restrictEdges_reachable_real p S hS] at h
  exact h hconn s hδ

end CriticalPercolation.BondGraph
end
end
end

end OAI
