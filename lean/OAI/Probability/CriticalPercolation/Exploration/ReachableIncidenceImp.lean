import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.ForceFalseSubset

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*}

lemma reachable_of_incidence_imp (G : BondGraph V E) (ω η : Set E) (a : V)
    (h : ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v) → η e → ω e)
    {b : V} (hab : (G.openGraph η).Reachable a b) : (G.openGraph ω).Reachable a b := by
  have hp := ((G.openGraph η).reachable_iff_reflTransGen a b).mp hab
  clear hab
  induction hp with
  | refl => exact .refl _
  | @tail v b _ hvb ih =>
    obtain ⟨⟨e,he,hee⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvb
    have hv : v ∈ G.ends e := by simp [hee]
    have hadj : (G.openGraph ω).Adj v b :=
      (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,h e ⟨v,hv,ih⟩ he,hee⟩,hne⟩
    exact ih.trans hadj.reachable

lemma reachable_incidence_congr (G : BondGraph V E) (ω η : Set E) (a : V)
    (h : ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v) → (ω e ↔ η e))
    (b : V) : (G.openGraph ω).Reachable a b ↔ (G.openGraph η).Reachable a b := by
  have hback : ∀ b, (G.openGraph η).Reachable a b → (G.openGraph ω).Reachable a b :=
    fun _ => G.reachable_of_incidence_imp ω η a (fun e he => (h e he).mpr)
  constructor
  · apply G.reachable_of_incidence_imp η ω a
    intro e he
    exact (h e (by obtain ⟨v,hv,har⟩ := he; exact ⟨v,hv,hback v har⟩)).mp
  · exact hback b

lemma reachable_delete_incidence_congr (G : BondGraph V E) (ω η : Set E) (a : V)
    (h : ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v) → (ω e ↔ η e))
    (e : E) (b : V) :
    (G.openGraph (Function.update ω e False)).Reachable a b ↔
      (G.openGraph (Function.update η e False)).Reachable a b := by
  apply G.reachable_incidence_congr
  intro f hf
  by_cases hfe : f = e
  · subst f; erw [Function.update_self,Function.update_self]
  · erw [Function.update_of_ne hfe,Function.update_of_ne hfe]
    obtain ⟨v,hv,har⟩ := hf
    exact h f ⟨v,hv,G.reachable_of_incidence_imp ω (Function.update ω e False) a
      (fun edge _ => force_false_subset ω e edge) har⟩

end CriticalPercolation.BondGraph

end
end

end OAI
