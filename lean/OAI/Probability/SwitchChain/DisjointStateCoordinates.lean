import OAI.Probability.SwitchChain.DisjointFiberCoordinates

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {n : Nat} {d : Fin n → Nat}

theorem graphDegree_eq_simpleDegree (G : SimpleGraph (Fin n)) (v : Fin n) :
    graphDegree G v = G.degree v := by
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

abbrev StateCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  {H : GraphState n d // SameCell e G.val H.val}

def stateCellDegreeEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ DegreeCell e G.val where
  toFun H := ⟨H.val.val, H.property, fun v => by
    rw [← graphDegree_eq_simpleDegree, ← graphDegree_eq_simpleDegree]
    exact (H.val.property v).trans (G.property v).symm⟩
  invFun H := ⟨⟨H.val, fun v => by
    rw [graphDegree_eq_simpleDegree, H.property.2 v, ← graphDegree_eq_simpleDegree]
    exact G.property v⟩, H.property.1⟩
  left_inv H := rfl
  right_inv H := rfl

def stateCellEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ FeasibleCoordinates e G.val :=
  (stateCellDegreeEquiv e G).trans (degreeCellEquiv e G.val)

@[simp] theorem stateCellEquiv_matrix (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellEquiv e G H).matrix = crossCode e H.val.val := rfl

@[simp] theorem stateCellEquiv_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellEquiv e G H).left = leftAssignment e G.val H.val.val := rfl

@[simp] theorem stateCellEquiv_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellEquiv e G H).right = rightAssignment e G.val H.val.val := rfl

@[simp] theorem stateCellEquiv_symm_graph (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (c : FeasibleCoordinates e G.val) :
    ((stateCellEquiv e G).symm c).val.val =
      realizeCoordinates e G.val c.matrix c.left c.right := rfl

theorem stateCellEquiv_sameFiber_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H K : StateCell e G) :
    PairResampling.SameFiber {e 0, e 1} H.val.val K.val.val ↔
      (stateCellEquiv e G H).right = (stateCellEquiv e G K).right :=
  sameFiber_left_iff_rightAssignment_eq e G H.val K.val H.property K.property

theorem stateCellEquiv_sameFiber_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H K : StateCell e G) :
    PairResampling.SameFiber {e 2, e 3} H.val.val K.val.val ↔
      (stateCellEquiv e G H).left = (stateCellEquiv e G K).left :=
  sameFiber_right_iff_leftAssignment_eq e G H.val K.val H.property K.property

end Problem315.DisjointEncoding

end

end OAI
