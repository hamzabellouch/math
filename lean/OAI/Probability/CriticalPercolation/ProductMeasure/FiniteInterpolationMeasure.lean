import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.FiniteInterpolationUniform
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Fintype E]

lemma prob_eq_real (q : E → unitInterval) (A : Set (Set E)) :
    FiniteProduct.prob (fun e => bitWeight (q e)) (fun ω => ω ∈ A) = (law q).real A := by
  rw [real_eq_expect_indicator]
  unfold FiniteProduct.prob
  rfl

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoClusterEvent (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.openGraph ω).Reachable u v} ∩ G.clusterTail u s ∩ G.clusterTail v s

lemma measurableSet_twoClusterEvent [Countable V] [Countable E] (u v : V) (s : ℕ) :
    MeasurableSet (G.twoClusterEvent u v s) := by
  exact ((G.measurable_reachable u v).setOf.compl.inter
    (G.measurableSet_clusterTail u s)).inter (G.measurableSet_clusterTail v s)

lemma clusterTail_iff_card [Fintype V] (ω : Set E) (u : V) (s : ℕ) :
    ω ∈ G.clusterTail u s ↔ s ≤ (G.cluster ω u).toFinset.card := by
  constructor
  · rintro ⟨K,hK,hsub,hs⟩
    exact hs.trans (by simpa only [Set.ncard_eq_toFinset_card'] using Set.ncard_le_ncard hsub)
  · intro hs
    exact ⟨G.cluster ω u, Set.toFinite _, Set.Subset.rfl, by simpa only [Set.ncard_eq_toFinset_card'] using hs⟩

lemma twoClusterEvent_iff_endpoint [Fintype V] (ω : Set E) (u v : V) (s : ℕ) :
    ω ∈ G.twoClusterEvent u v s ↔ BinaryLaw.endpointEvent G u v s ω := by
  simp only [twoClusterEvent, Set.mem_inter_iff, Set.mem_ofPred_eq,
    clusterTail_iff_card, BinaryLaw.endpointEvent, and_assoc]

lemma finite_endpoint_prob [Fintype V] [Fintype E] (p : unitInterval) (u v : V) (s : ℕ) :
    FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
      (BinaryLaw.endpointEvent G u v s) = (G.law p).real (G.twoClusterEvent u v s) := by
  rw [law, ← BernoulliProduct.law_const, ← BernoulliProduct.prob_eq_real]
  congr 1
  funext ω
  exact propext (G.twoClusterEvent_iff_endpoint ω u v s).symm

theorem finite_interpolation_measure [Fintype V] [Fintype E]
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0<c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real (G.twoClusterEvent (x 0) (x d) s)) :
    ∃ j<d, 0 < (G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real (G.twoClusterEvent (x 0) (x d) s))+Nat.clog 2 d+1) := by
  have h := BinaryLaw.finite_interpolation_uniform G d x hd hp
    (fun _ : E => BernoulliProduct.bitWeight p)
    (fun _ => by simp [BernoulliProduct.bitWeight])
    (fun _ => by simp [BernoulliProduct.bitWeight]) hc hε hεp hεq
  simp_rw [G.finite_endpoint_prob p] at h
  apply h
  intro j k hj hk hjk
  change c ≤ FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
    (fun ω => ω ∈ {η | (G.openGraph η).Reachable (x j) (x k)})
  rw [BernoulliProduct.prob_eq_real, BernoulliProduct.law_const]
  exact hconn j k hj hk hjk
  exact hδ

end BondGraph
end CriticalPercolation
end
end
end

end OAI
