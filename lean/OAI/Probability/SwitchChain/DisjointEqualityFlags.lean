import OAI.Probability.SwitchChain.DisjointStateLaw
import OAI.Probability.SwitchChain.PairEqualityProjection

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

private theorem row_crossCode (e : Fin 4 ↪ Fin n) (H : SimpleGraph (Fin n)) (i : Fin 2) :
    CrossBlock.row (crossCode e H) i =
      edgeBit H (e (leftIndex i)) (e 2) + edgeBit H (e (leftIndex i)) (e 3) := by
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq, edgeBit]
  rfl

private theorem col_crossCode (e : Fin 4 ↪ Fin n) (H : SimpleGraph (Fin n)) (j : Fin 2) :
    CrossBlock.col (crossCode e H) j =
      edgeBit H (e 0) (e (rightIndex j)) + edgeBit H (e 1) (e (rightIndex j)) := by
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq, edgeBit]
  rfl

theorem equality_crossTotal_eq (e : Fin 4 ↪ Fin n) (H : GraphState n d) :
    PairEquality.crossTotal (e 0) (e 1) (e 2) (e 3) H =
      CrossBlock.total (crossCode e H.val) := by
  rw [CrossBlock.total_eq_row_add, row_crossCode, row_crossCode]
  change (PairFiber.edgeBit H.val (e 0) (e 2) + PairFiber.edgeBit H.val (e 1) (e 2)) +
      (PairFiber.edgeBit H.val (e 0) (e 3) + PairFiber.edgeBit H.val (e 1) (e 3)) =
    (edgeBit H.val (e 0) (e 2) + edgeBit H.val (e 0) (e 3)) +
      (edgeBit H.val (e 1) (e 2) + edgeBit H.val (e 1) (e 3))
  simp only [PairFiber.edgeBit, edgeBit]
  omega

theorem stateLeftData_margin (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateLeftData e G H).val.1.val = CrossBlock.row (crossCode e H.val.val) 0 := rfl

theorem stateRightData_margin (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateRightData e G H).val.1.val = CrossBlock.col (crossCode e H.val.val) 0 := rfl

theorem stateLeftFlag_eq_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    flag (stateLeftData e G H).val.1 =
      PairEquality.observable (e 0) (e 2) (e 3) H.val := by
  have hmargin := stateLeftData_margin e G H
  have heq : (stateLeftData e G H).val.1 = 1 ↔
      CrossBlock.row (crossCode e H.val.val) 0 = 1 := by
    exact (Fin.ext_iff).trans (by rw [hmargin]; rfl)
  unfold flag
  simp only [heq]
  change (if CrossBlock.row (crossCode e H.val.val) 0 = 1 then (0 : ℝ) else 1) =
    if H.val.val.Adj (e 0) (e 2) ↔ H.val.val.Adj (e 0) (e 3) then 1 else 0
  rw [row_crossCode]
  change (if edgeBit H.val.val (e 0) (e 2) + edgeBit H.val.val (e 0) (e 3) = 1 then (0 : ℝ) else 1) = _
  by_cases h0 : H.val.val.Adj (e 0) (e 2) <;>
    by_cases h1 : H.val.val.Adj (e 0) (e 3) <;>
    simp [edgeBit, h0, h1]

theorem stateRightFlag_eq_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    flag (stateRightData e G H).val.1 =
      PairEquality.observable (e 2) (e 0) (e 1) H.val := by
  have hmargin := stateRightData_margin e G H
  have heq : (stateRightData e G H).val.1 = 1 ↔
      CrossBlock.col (crossCode e H.val.val) 0 = 1 := by
    exact (Fin.ext_iff).trans (by rw [hmargin]; rfl)
  unfold flag
  simp only [heq]
  change (if CrossBlock.col (crossCode e H.val.val) 0 = 1 then (0 : ℝ) else 1) =
    if H.val.val.Adj (e 2) (e 0) ↔ H.val.val.Adj (e 2) (e 1) then 1 else 0
  have hc0 : H.val.val.Adj (e 2) (e 0) ↔ H.val.val.Adj (e 0) (e 2) :=
    H.val.val.adj_comm _ _
  have hc1 : H.val.val.Adj (e 2) (e 1) ↔ H.val.val.Adj (e 1) (e 2) :=
    H.val.val.adj_comm _ _
  rw [hc0,hc1]
  rw [col_crossCode]
  change (if edgeBit H.val.val (e 0) (e 2) + edgeBit H.val.val (e 1) (e 2) = 1 then (0 : ℝ) else 1) = _
  by_cases h0 : H.val.val.Adj (e 0) (e 2) <;>
    by_cases h1 : H.val.val.Adj (e 1) (e 2) <;>
    simp [edgeBit, h0, h1]

theorem stateCell_crossTotal_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    CrossBlock.total (crossCode e H.val.val) = CrossBlock.total (crossCode e G.val) :=
  ((coordinate_degrees_iff e G.val
    (graphStateCellEquiv e G H).matrix (graphStateCellEquiv e G H).left
    (graphStateCellEquiv e G H).right (graphStateCellEquiv e G H).left_subset
    (graphStateCellEquiv e G H).right_subset).mp (graphStateCellEquiv e G H).degrees).1

theorem equality_crossTotal_on_cell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    PairEquality.crossTotal (e 0) (e 1) (e 2) (e 3) H.val =
      CrossBlock.total (crossCode e G.val) := by
  rw [equality_crossTotal_eq, stateCell_crossTotal_eq]

theorem equality_crossTotal_reverse_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    PairEquality.crossTotal (e 2) (e 3) (e 0) (e 1) G =
      CrossBlock.total (crossCode e G.val) := by
  rw [← equality_crossTotal_eq e G]
  unfold PairEquality.crossTotal PairFiber.edgeBit
  simp only [G.val.adj_comm (e 2) (e 0), G.val.adj_comm (e 3) (e 0),
    G.val.adj_comm (e 2) (e 1), G.val.adj_comm (e 3) (e 1)]
  omega

theorem equality_crossTotal_reverse_on_cell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    PairEquality.crossTotal (e 2) (e 3) (e 0) (e 1) H.val =
      CrossBlock.total (crossCode e G.val) := by
  rw [equality_crossTotal_reverse_eq, stateCell_crossTotal_eq]

end Problem315.DisjointMarginal

end

end OAI
