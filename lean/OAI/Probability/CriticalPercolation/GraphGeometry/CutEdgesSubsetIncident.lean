import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Clusters.ClusterObject
import OAI.Probability.CriticalPercolation.GraphGeometry.CutEdges

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

lemma cutEdges_subset_incidentEdges (G : BondGraph V E) (O : Set V) :
    G.cutEdges O ⊆ G.incidentEdges O := by
  rintro e ⟨x,y,he,_,hy⟩
  exact ⟨y,hy,by simp [he]⟩

lemma eraseVertices_agree_of_cutClosed (G : BondGraph V E) (O : Set V) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) {v z : V} {e : E}
    (hv : v ∉ O) (he : G.ends e = s(v,z)) :
    ω e = G.eraseVertices ω O e := by
  apply propext
  constructor
  · intro hω
    refine ⟨hω,?_⟩
    rintro ⟨u,hu,hue⟩
    have : u = v ∨ u = z := by simpa only [he,Sym2.mem_iff] using hue
    rcases this with rfl | rfl
    · exact hv hu
    · exact hc e ⟨v,_,he,hv,hu⟩ hω
  · exact fun h => h.1

end CriticalPercolation.BondGraph

end
end

end OAI
