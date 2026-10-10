import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Clusters.ThreeClusterAvoidanceSecond
import OAI.Probability.CriticalPercolation.Exploration.PivotalComparison
import OAI.Probability.CriticalPercolation.GraphGeometry.IsolateThree
import OAI.Probability.CriticalPercolation.ProductMeasure.ClosedThin

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E) [Fintype V] [Fintype E]

lemma threeCluster_avoidance_general (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) :
    prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair a s t) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) :=
  prob_mul_le_of_strict w hw hp _ _ _ _ (fun w' hw' hp' hc' =>
    G.threeCluster_avoidance w' hw' hp' hc' a s t b has hat)

lemma threeCluster_avoidance_second_general (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (hat : t ≠ a) (hst : t ≠ s) :
    prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair t a s) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
  have h := G.threeCluster_avoidance_general w hw hp t a s b hat hst
  rw [prob_congr w (G.separateThree_rotate a s t),
    prob_congr w (fun ω => and_congr_left (fun _ => G.separateThree_rotate a s t ω))] at h
  exact h

theorem residual_converted_variance_general (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hparam : p ∈ Set.Ioo 0 1) :
    let u := prob w (G.separateThree a s t)
    let v := prob w (G.joinedPair a s t)
    let α := prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b)
    let β := prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
    let γ := prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b)
    let σ := prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b)
    p*(1-p)*α*(α+σ) ≤
      p*(1-p)*(u+v)*(u+v-β-γ)/((1-p)*(u+v)+p*(u+v-β-γ)) *
        ((v+α-γ)/(u+v-β-γ)-v/(u+v))^2 := by
  dsimp only
  have h1 := G.threeCluster_avoidance_general w hw hp a s t b has hat
  have h2 := G.threeCluster_avoidance_second_general w hw hp a s t b hat.symm hst.symm
  have h3 := G.threeCluster_harris w hw hp a s t
  have h4 := G.threeCluster_event_bounds w hp a s t b
  apply DFS.converted_variance hparam (prob_nonneg w hp _) (prob_nonneg w hp _)
    (prob_nonneg w hp _) (prob_nonneg w hp _) (prob_nonneg w hp _) (prob_nonneg w hp _)
    h4.1 h4.2 _ h2 h3
  simpa only [mul_comm] using h1

end CriticalPercolation.BondGraph

end
end

end OAI
