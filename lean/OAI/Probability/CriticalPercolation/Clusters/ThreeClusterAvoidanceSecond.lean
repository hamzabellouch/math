import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.IsolateThree
import OAI.Probability.CriticalPercolation.ProductMeasure.ProbDisjoint

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

lemma threeCluster_avoidance_second (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z) (hc : ∀ e, 0 < w e False)
    (a s t b : V) (hat : t ≠ a) (hst : t ≠ s) :
    prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair t a s) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
  have h := G.threeCluster_avoidance w hw hp hc t a s b hat hst
  rw [prob_congr w (G.separateThree_rotate a s t),
    prob_congr w (fun ω => and_congr_left (fun _ => G.separateThree_rotate a s t ω))] at h
  exact h

omit [Fintype V] in
lemma threeCluster_event_bounds (w : E → Prop → ℝ) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) :
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) ≤
      prob w (G.separateThree a s t) ∧
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) ≤
      prob w (G.separateThree a s t) + prob w (G.joinedPair a s t) -
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) -
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  constructor
  · exact prob_mono w hp (fun _ h => h.1)
  · have h1 := prob_disjoint_le w hp
      (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b)
      (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
      (G.separateThree a s t) (fun _ h => h.1) (fun _ h => h.1)
      (fun _ h => h.1.1.1.2 (h.2.2.trans h.1.2.symm))
    have h2 := prob_mono w hp (P := fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b)
      (Q := G.joinedPair a s t) (fun _ h => h.1)
    linarith

end CriticalPercolation.BondGraph

end
end

end OAI
