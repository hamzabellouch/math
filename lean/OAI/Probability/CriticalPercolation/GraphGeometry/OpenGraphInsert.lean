import Mathlib
import OAI.Probability.CriticalPercolation.Model

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*}

lemma openGraph_insert (G : BondGraph V E) (s : Set E) (e : E) (a b : V)
    (he : G.ends e = s(a,b)) :
    G.openGraph (insert e s) = G.openGraph s ⊔ SimpleGraph.edge a b := by
  rw [openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma openGraph_delete_eq_update (G : BondGraph V E) [DecidableEq E]
    (ω : E → Bool) (f : E) :
    G.openGraph {e | e ≠ f ∧ ω e = true} =
      G.openGraph {e | Function.update ω f false e = true} := by
  congr 1
  ext e
  by_cases he : e = f
  · subst e; simp
  · simp [he]

lemma openGraph_delete_sup (G : BondGraph V E) (ω : E → Bool)
    (f : E) (a z : V) (hf : ω f = true) (he : G.ends f = s(a,z)) :
    G.openGraph {e | ω e = true} =
      G.openGraph {e | e ≠ f ∧ ω e = true} ⊔ SimpleGraph.edge a z := by
  have hh : {e | ω e = true} = insert f {e | e ≠ f ∧ ω e = true} := by
    ext e
    by_cases h : e = f
    · subst e; simp [hf]
    · simp [h]
  rw [hh,openGraph_insert G _ _ _ _ he]
end CriticalPercolation.BondGraph

end
end

end OAI
