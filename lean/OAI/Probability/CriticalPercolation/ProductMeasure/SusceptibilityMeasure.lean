import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure
import OAI.Probability.CriticalPercolation.Criticality.FiniteSusceptibility
import OAI.Probability.CriticalPercolation.Modular.FiniteClusterTransport
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteAdjacentMeasure

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma finite_clusterTail_measure_bound [Fintype V] [Fintype E]
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (u : V) (s : ℕ) :
    (s:ℝ)*(G.law p).real (G.clusterTail u s) ≤ 2 := by
  let w := fun _ : E => BernoulliProduct.bitWeight p
  have hn : ∀ e b, 0≤w e b := fun _ => BernoulliProduct.bitWeight_nonneg p
  have ht := G.finite_susceptibility_bound p p.property w
    (fun _ => BernoulliProduct.bitWeight_sum p) hn
    (fun _ => by simp only [w,BernoulliProduct.bitWeight,ite_false])
    (fun _ => by simp only [w,BernoulliProduct.bitWeight,ite_true]) D
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) hpD u
  have hprob : (G.law p).real (G.clusterTail u s) = prob w (fun ω => ω∈G.clusterTail u s) := by
    simpa only [law,← BernoulliProduct.law_const,w] using
      (BernoulliProduct.prob_eq_real (fun _ : E => p) (G.clusterTail u s)).symm
  rw [hprob,prob,← expect_const_mul]
  refine le_trans (expect_mono hn ?_) ht
  intro ω
  change (s:ℝ)*(if {e | ω e}∈G.clusterTail u s then 1 else 0) ≤
    (G.clusterSize {e | ω e} u : ℝ)
  by_cases hh : {e | ω e} ∈ G.clusterTail u s
  · simp only [ite_eq_left hh,mul_one]
    exact_mod_cast (G.clusterTail_iff_card {e | ω e} u s).mp hh
  · simp only [ite_eq_right hh,mul_zero]
    exact Nat.cast_nonneg _

lemma induce_clusterTail_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (u : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).clusterTail u s) =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} := by
  have he : (G.induce S).clusterTail u s =
      {ω | Subtype.val '' ω ∈ G.clusterTail u.val s} := by
    ext ω
    exact G.induce_clusterTail S ω u s
  rw [he,G.induce_law_event S hS]

lemma induced_clusterTail_measure_bound (hlocal : G.LocallyFinite)
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (S : Set V) (hS : S.Finite) (u : S) (s : ℕ) :
    (s:ℝ)*(G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} ≤ 2 := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  have h := (G.induce S).finite_clusterTail_measure_bound p D
    (G.induce_incident_bound hlocal D hD S) hpD u s
  rwa [G.induce_clusterTail_real S (G.finite_inducedEdges hlocal hS)] at h

end CriticalPercolation.BondGraph
end
end
end

end OAI
