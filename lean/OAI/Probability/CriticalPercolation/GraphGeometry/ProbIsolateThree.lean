import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.IsolateThree
import OAI.Probability.CriticalPercolation.GraphGeometry.Link
import OAI.Probability.CriticalPercolation.ProductMeasure.ProbOr
import OAI.Probability.CriticalPercolation.Clusters.ThreeClusterAvoidanceGeneral

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E) [Fintype E]

lemma prob_isolateThree (w : E → Prop → ℝ) (a s t : V) :
    prob w (G.isolateThree a s t) =
      prob w (G.separateThree a s t) + prob w (G.joinedPair a s t) := by
  have hh := prob_split w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable s t)
  exact hh.trans (add_comm _ _)

lemma prob_wired_pivot (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t) =
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) +
    prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b) := by
  rw [← prob_or w _ _ (by
    intro ω ⟨h,k⟩
    exact h.1.1.1 k.1.2)]
  apply prob_congr
  intro ω
  rw [Wiring.wired_pivot]
  dsimp only [separateThree,joinedPair,isolateThree]
  have hat : (G.openGraph ω).Reachable t a ↔ (G.openGraph ω).Reachable a t := SimpleGraph.reachable_comm
  have hst : (G.openGraph ω).Reachable t s ↔ (G.openGraph ω).Reachable s t := SimpleGraph.reachable_comm
  have hbt : (G.openGraph ω).Reachable b t ↔ (G.openGraph ω).Reachable t b := SimpleGraph.reachable_comm
  simp only [hat,hst,hbt]
  tauto

lemma prob_two_pivots (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) =
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
  apply prob_congr
  intro ω
  rw [Wiring.two_pivots]
  dsimp only [separateThree,isolateThree]
  have hbt : (G.openGraph ω).Reachable b t ↔ (G.openGraph ω).Reachable t b := SimpleGraph.reachable_comm
  simp only [hbt]
  tauto

lemma prob_wired_avoid (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) =
    prob w (G.isolateThree a s t) -
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) -
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  rw [prob_congr w (fun ω => Wiring.avoid_sup_edge (G.openGraph ω) a s t b)]
  have hsplit := prob_split w
    (fun ω => G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
    (fun ω => (G.openGraph ω).Reachable s t)
  have hleft : prob w (fun ω =>
      (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧ (G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair]; tauto)
  have hright : prob w (fun ω =>
      (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧ ¬(G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [separateThree]; tauto)
  rw [hleft,hright] at hsplit
  have hh := prob_diff w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable a b)
  have he : prob w (fun ω => ¬(G.openGraph ω).Reachable a s ∧
      ¬(G.openGraph ω).Reachable a t ∧ ¬(G.openGraph ω).Reachable a b) =
      prob w (fun ω => G.isolateThree a s t ω ∧ ¬(G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [isolateThree]; tauto)
  rw [he,hh,hsplit]
  ring

lemma prob_wired_avoid_target (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable s t) =
    prob w (G.joinedPair a s t) +
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) -
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  rw [prob_congr w (fun ω => Wiring.avoid_target_sup_edge (G.openGraph ω) a s t b)]
  rw [prob_or w _ _ (by intro ω ⟨h,k⟩; exact k.2.2.1 h.2.2.1)]
  have hleft : prob w (fun ω => ¬(G.openGraph ω).Reachable a s ∧
      ¬(G.openGraph ω).Reachable a t ∧ (G.openGraph ω).Reachable s t ∧
      ¬(G.openGraph ω).Reachable a b) =
      prob w (fun ω => G.joinedPair a s t ω ∧ ¬(G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair,isolateThree]; tauto)
  have hright : prob w (fun ω => ¬(G.openGraph ω).Reachable a s ∧
      ¬(G.openGraph ω).Reachable a t ∧ ¬(G.openGraph ω).Reachable s t ∧ (G.openGraph ω).Reachable b t) =
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
    apply prob_congr
    intro ω
    dsimp [separateThree,isolateThree]
    have hbt : (G.openGraph ω).Reachable b t ↔ (G.openGraph ω).Reachable t b := SimpleGraph.reachable_comm
    simp only [hbt]
    tauto
  rw [hleft,hright,prob_diff]
  ring

variable [Fintype V]

theorem wired_pair_charge (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hparam : p ∈ Set.Ioo 0 1) :
    let U0 := prob w (G.isolateThree a s t)
    let U1 := prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t)
    let R0 := prob w (G.joinedPair a s t)
    let R1 := prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable s t)
    let de := prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t)
    let pair := prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t)
    p*(1-p)*pair*de ≤ p*(1-p)*U0*U1/((1-p)*U0+p*U1)*(R1/U1-R0/U0)^2 := by
  dsimp only
  rw [G.prob_wired_pivot,G.prob_two_pivots,G.prob_wired_avoid,G.prob_wired_avoid_target,
    G.prob_isolateThree]
  exact G.residual_converted_variance_general w hw hp a s t b has hat hst hparam

end CriticalPercolation.BondGraph

open scoped Classical

end
end

end OAI
