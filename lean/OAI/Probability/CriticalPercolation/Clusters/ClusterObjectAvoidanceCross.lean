import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterObject
import OAI.Probability.CriticalPercolation.Modular.ObjectAvoidMass

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct FiniteMarkov
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

theorem clusterObject_avoidance_cross_mul (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (hc : ∀ e, 0 < w e False) {A B : Set V} (hAB : Disjoint A B)
    (f g : ClusterObject V E → ℝ) (hf : Monotone f) (hg : Monotone g) :
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      f (G.clusterObject ω A) * g (G.clusterObject ω B) else 0))*G.objectAvoidTotal w A B ≤
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0)) *
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then g (G.clusterObject ω B) else 0)) := by
  have hZ : 0 < G.objectAvoidTotal w A B :=
    (Finset.prod_pos fun e _ => hc e).trans_le (G.objectAvoidTotal_minorization w hp hAB)
  have hh := G.clusterObject_avoidance_cross w hw hp hc hAB f g hf hg
  have hi (F H Z : ℝ) : (F/Z)*(H/Z) = (F*H/Z)/Z := by ring
  rw [hi, div_le_div_iff_of_pos_right hZ] at hh
  exact (le_div_iff₀ hZ).mp hh

omit [Fintype V] [Fintype E] in
lemma openGraph_adj_clusterObject {ω : Set E} {S : Set V} {v t : V}
    (hv : v ∈ (G.clusterObject ω S).1) (ha : (G.openGraph ω).Adj v t) :
    (G.openGraph (G.clusterObject ω S).2).Adj v t := by
  obtain ⟨⟨e, he, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp ha
  exact (SimpleGraph.fromEdgeSet_adj _).mpr
    ⟨⟨e, ⟨he, v, hv, by simp [heq]⟩, heq⟩, hne⟩

omit [Fintype V] [Fintype E] in
lemma reachable_clusterObject {ω : Set E} {S : Set V} {v t : V} (hv : v ∈ S) :
    (G.openGraph (G.clusterObject ω S).2).Reachable v t ↔ (G.openGraph ω).Reachable v t := by
  constructor
  · intro ht
    exact ht.mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono Set.inter_subset_left))
  · intro ht
    have h := ((G.openGraph ω).reachable_iff_reflTransGen v t).mp ht
    clear ht
    induction h with
    | refl => exact .refl _
    | @tail u t h hut ih =>
      exact ih.trans (G.openGraph_adj_clusterObject
        ⟨v, hv, ((G.openGraph ω).reachable_iff_reflTransGen v u).mpr h⟩ hut).reachable

end CriticalPercolation.BondGraph

end
end

end OAI
