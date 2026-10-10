import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.Link

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

lemma force_false_subset (ω : Set E) (e : E) :
    ∀ f, Function.update ω e False f → ω f := by
  intro f hf
  by_cases he : f = e
  · subst f; erw [Function.update_self] at hf; exact hf.elim
  · erw [Function.update_of_ne he] at hf; exact hf

lemma reachable_force_false_of_not_reachable (G : BondGraph V E) (ω : Set E)
    (e : E) (r : V) (hr : r ∈ G.ends e) {x y : V}
    (hxr : ¬(G.openGraph ω).Reachable x r) (hxy : (G.openGraph ω).Reachable x y) :
    (G.openGraph (Function.update ω e False)).Reachable x y := by
  have hh := ((G.openGraph ω).reachable_iff_reflTransGen x y).mp hxy
  clear hxy
  induction hh with
  | refl => exact .refl _
  | @tail v y hpath hvy ih =>
    have hxv := ((G.openGraph ω).reachable_iff_reflTransGen x v).mpr hpath
    obtain ⟨⟨f,hf,hfe⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvy
    have hfe' : f ≠ e := by
      intro he
      subst f
      have : r = v ∨ r = y := by simpa only [hfe,Sym2.mem_iff] using hr
      rcases this with rfl | rfl
      · exact hxr hxv
      · exact hxr (hxv.trans hvy.reachable)
    apply ih.trans
    apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨f,?_,hfe⟩,hne⟩
    change Function.update ω e False f
    erw [Function.update_of_ne hfe']
    exact hf

lemma target_after_open_iff (G : BondGraph V E) (ω : Set E) (B : Set V)
    (a u v : V) (f : E) (hf : G.ends f = s(u,v))
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (hva : ¬(G.openGraph ω).Reachable a v) :
    (∃ b ∈ B, (G.openGraph (Function.update ω f True)).Reachable a b) ↔
      (G.openGraph ω).Reachable a u := by
  have updated : (Function.update ω f True : Set E) = insert f ω := by
    ext bond
    by_cases equal : bond = f
    · subst bond
      erw [Function.update_self]
      exact iff_of_true trivial (Set.mem_insert f ω)
    · erw [Function.update_of_ne equal]
      change bond ∈ ω ↔ bond ∈ insert f ω
      simp [equal]
  have forced : G.openGraph (Function.update ω f True) =
      G.openGraph ω ⊔ SimpleGraph.edge u v := by
    erw [updated]
    rw [openGraph, Set.image_insert_eq, hf, ← Set.singleton_union,
      SimpleGraph.fromEdgeSet_union]
    exact sup_comm _ _
  rw [forced]
  constructor
  · rintro ⟨b,hb,hab⟩
    rcases (Wiring.reachable_sup_edge (G.openGraph ω) u v a b).mp hab with h | ⟨h,_⟩ | ⟨h,_⟩
    · exact (hn ⟨b,hb,h⟩).elim
    · exact h
    · exact (hva h).elim
  · intro hau
    obtain ⟨b,hb,hvb⟩ := hv
    exact ⟨b,hb,(Wiring.reachable_sup_edge (G.openGraph ω) u v a b).mpr
      (Or.inr (Or.inl ⟨hau,hvb⟩))⟩

end CriticalPercolation.BondGraph

end
end

end OAI
