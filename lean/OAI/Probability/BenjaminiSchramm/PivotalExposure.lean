import OAI.Probability.BenjaminiSchramm.ClusterExposure
import OAI.Probability.BenjaminiSchramm.EdgeClosing

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exactCluster_boundary_closed {ω : Set E} {x u v : V} {S : Set V} {e : E}
    (hends : G.ends e = s(u,v)) (hu : u ∈ S) (hv : v ∉ S)
    (hS : G.cluster ω x = S) : e ∉ ω := by
  intro he
  have huv : u ≠ v := fun huv => hv (huv ▸ hu)
  have hadj : (G.openGraph ω).Adj u v :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,hends⟩,huv⟩
  have hxu : (G.openGraph ω).Reachable x u := by
    change u ∈ G.cluster ω x
    rwa [hS]
  exact hv (hS ▸ (hxu.trans hadj.reachable))

theorem closed_cluster_pivotal_factor [Countable V] [Countable E]
    (p : unitInterval) (hp : (p : ℝ) < 1) (x : V) (S : Set V) (e : E)
    (u v : V) (hends : G.ends e = s(u,v)) (hu : u ∈ S) (hv : v ∉ S)
    (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∈ ω then
      ({η | G.cluster η x = S} : Set (Set E)).indicator
        (fun η => F (G.eraseVertices η S)) (BernoulliProduct.forceOn {e} ∅ ω)
      else 0 ∂G.law p) =
        (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
          G.law p {ω | G.cluster ω x = S} *
            ∫⁻ η, F (G.eraseVertices η S) ∂G.law p := by
  let f : Set E → ℝ≥0∞ := ({η | G.cluster η x = S} : Set (Set E)).indicator
    (fun η => F (G.eraseVertices η S))
  have hf : Measurable f := (hF.comp (G.measurable_eraseVertices S)).indicator
    (G.measurableSet_exactCluster x S)
  have heq : (fun ω => if e ∉ ω then f ω else 0) = f := by
    funext ω
    by_cases hS : G.cluster ω x = S
    · rw [ite_eq_left (G.exactCluster_boundary_closed hends hu hv hS)]
    · simp only [f, Set.indicator, Set.mem_ofPred_eq, ite_eq_right hS, ite_self]
  have hclose := BernoulliProduct.lintegral_edge_closing (fun _ : E => p) e hp f hf
  rw [heq] at hclose
  have hlaw : BernoulliProduct.law (fun _ : E => p) = G.law p :=
    BernoulliProduct.law_const p
  rw [hlaw] at hclose
  change (∫⁻ ω, if e ∈ ω then f (BernoulliProduct.forceOn {e} ∅ ω) else 0 ∂G.law p) = _
  rw [hclose]
  change _ * (∫⁻ ω, ({ω | G.cluster ω x = S} : Set (Set E)).indicator
    (fun ω => F (G.eraseVertices ω S)) ω ∂G.law p) = _
  rw [G.exactCluster_exterior_factor p x S F hF, mul_assoc]

end CriticalPercolation.BondGraph

end

end OAI
