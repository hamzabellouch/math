import OAI.Probability.SwitchChain.DisjointRealization
import OAI.Probability.SwitchChain.Definitions

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

private theorem qualified_degree (n : Nat) (G : SimpleGraph (Fin n)) (v : Fin n) :
    graphDegree G v = G.degree v := by
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

def stateCellToDegreeCell {n : Nat} {d : Fin n → Nat}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    {H : GraphState n d // SameCell e G.val H.val} ≃ DegreeCell e G.val where
  toFun H := ⟨H.val.val, H.property, by
    intro v
    rw [← qualified_degree, ← qualified_degree]
    exact (H.val.property v).trans (G.property v).symm⟩
  invFun H := ⟨⟨H.val, by
    intro v
    rw [qualified_degree, H.property.2 v, ← qualified_degree]
    exact G.property v⟩, H.property.1⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv H := by apply Subtype.ext; rfl

def graphStateCellEquiv {n : Nat} {d : Fin n → Nat}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    {H : GraphState n d // SameCell e G.val H.val} ≃ FeasibleCoordinates e G.val :=
  (stateCellToDegreeCell e G).trans (degreeCellEquiv e G.val)

end Problem315.DisjointEncoding

end

end OAI
