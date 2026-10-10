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
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

noncomputable def eraseBond (f : E) (o : V) : BondGraph V E :=
  ⟨Function.update G.ends f s(o,o)⟩

lemma eraseBond_ends_ne (f : E) (o : V) {e : E} (he : e ≠ f) :
    (G.eraseBond f o).ends e = G.ends e := by simp [eraseBond,he]

lemma eraseBond_openGraph (f : E) (o : V) (ω : Set E) :
    (G.eraseBond f o).openGraph ω = G.openGraph {e | e ≠ f ∧ e ∈ ω} := by
  ext u v
  unfold openGraph
  rw [SimpleGraph.fromEdgeSet_adj,SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e,he,hev⟩,huv⟩
    have hef : e ≠ f := by
      intro hh
      subst e
      simp only [eraseBond,Function.update_self] at hev
      have hd := (Sym2.eq_iff.mp hev)
      rcases hd with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact huv (h1.symm.trans h2)
      · exact huv (h2.symm.trans h1)
    exact ⟨⟨e,⟨hef,he⟩,(G.eraseBond_ends_ne f o hef).symm.trans hev⟩,huv⟩
  · rintro ⟨⟨e,⟨hef,he⟩,hev⟩,huv⟩
    exact ⟨⟨e,he,(G.eraseBond_ends_ne f o hef).trans hev⟩,huv⟩

lemma eraseBond_subgraph (f : E) (o : V) (ω : Set E) :
    (G.eraseBond f o).openGraph ω ≤ G.openGraph ω := by
  rw [G.eraseBond_openGraph]
  exact SimpleGraph.fromEdgeSet_mono (Set.image_mono (fun _ member => member.2))

lemma knownGraph_le_eraseBond (read : Finset E) (f : E) (o : V) (ω : Set E)
    (hf : f ∉ read) :
    G.openGraph {e | e ∈ read ∧ e ∈ ω} ≤ (G.eraseBond f o).openGraph ω := by
  rw [G.eraseBond_openGraph]
  apply SimpleGraph.fromEdgeSet_mono ∘ Set.image_mono
  intro e he
  exact ⟨fun hef => hf (hef ▸ he.1),he.2⟩

lemma openGraph_eq_eraseBond_sup (f : E) (o v z : V) (ω : Set E)
    (hf : f ∈ ω) (he : G.ends f = s(v,z)) :
    G.openGraph ω = (G.eraseBond f o).openGraph ω ⊔ SimpleGraph.edge v z := by
  rw [G.eraseBond_openGraph]
  have hh : ω = insert f {e | e ≠ f ∧ e ∈ ω} := by
    ext e
    by_cases h : e = f
    · subst e; simp [hf]
    · simp [h]
  conv_lhs => rw [hh]
  rw [openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma eraseBond_openGraph_force_false (f : E) (o : V) (ω : Set E) :
    (G.eraseBond f o).openGraph ω = G.openGraph (Function.update ω f False) := by
  rw [G.eraseBond_openGraph]
  congr 1
  ext e
  change (e ≠ f ∧ e ∈ ω) ↔ Function.update ω f False e
  by_cases h : e = f
  · subst e
    erw [Function.update_self]
    simp
  · erw [Function.update_of_ne h]
    change (e ≠ f ∧ e ∈ ω) ↔ e ∈ ω
    simp [h]

end CriticalPercolation.BondGraph

end
end

end OAI
