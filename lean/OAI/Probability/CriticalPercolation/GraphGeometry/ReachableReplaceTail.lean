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

namespace CriticalPercolation.Wiring
variable {V : Type*}

lemma reachable_replace_tail (H : SimpleGraph V) (s v b x y : V)
    (hsv : H.Reachable s v) :
    (H ⊔ SimpleGraph.edge v b).Reachable x y ↔
      (H ⊔ SimpleGraph.edge s b).Reachable x y := by
  rw [reachable_sup_edge,reachable_sup_edge]
  constructor
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1.trans hsv.symm,h2⟩)
    · exact Or.inr (Or.inr ⟨h1,hsv.trans h2⟩)
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1.trans hsv,h2⟩)
    · exact Or.inr (Or.inr ⟨h1,hsv.symm.trans h2⟩)

end CriticalPercolation.Wiring

namespace CriticalPercolation.BondGraph
variable {V E : Type*}

lemma openGraph_force_true (G : BondGraph V E) (ω : Set E) (e : E) (v b : V)
    (he : G.ends e = s(v,b)) :
    G.openGraph (Function.update ω e True) = G.openGraph ω ⊔ SimpleGraph.edge v b := by
  have hs : (Function.update ω e True : Set E) = insert e ω := by
    ext j
    by_cases hje : j = e
    · subst j; erw [Function.update_self]; exact iff_of_true trivial (Set.mem_insert e ω)
    · erw [Function.update_of_ne hje]
      change j ∈ ω ↔ j ∈ insert e ω
      simp [hje]
  erw [hs]
  rw [openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma openGraph_force_false_of_closed (G : BondGraph V E) (ω : Set E) (e : E)
    (he : ¬ω e) : G.openGraph (Function.update ω e False) = G.openGraph ω := by
  have hu : Function.update ω e False = ω := by
    have hb : ω e = False := propext (iff_false_intro he)
    rw [← hb]
    exact Function.update_eq_self _ _
  rw [hu]

end CriticalPercolation.BondGraph

end
end

end OAI
