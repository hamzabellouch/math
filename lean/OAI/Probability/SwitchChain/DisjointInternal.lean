import OAI.Probability.SwitchChain.DisjointReconstruct
import OAI.Probability.SwitchChain.CrossMatrix

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

def internalAdj (l r : Bool) (M : CrossBlock.Matrix) : Fin 4 → Fin 4 → Bool :=
  ![![false, l, M 0 0, M 0 1],
    ![l, false, M 1 0, M 1 1],
    ![M 0 0, M 1 0, false, r],
    ![M 0 1, M 1 1, r, false]]

def internalGraph (l r : Bool) (M : CrossBlock.Matrix) : SimpleGraph (Fin 4) where
  Adj a b := internalAdj l r M a b = true
  symm := by
    constructor
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [internalAdj]
  loopless := by
    constructor
    intro a h
    fin_cases a <;> simp_all [internalAdj]

@[simp] theorem internalGraph_left (l r : Bool) (M : CrossBlock.Matrix) :
    (internalGraph l r M).Adj 0 1 ↔ l = true := by simp [internalGraph, internalAdj]

@[simp] theorem internalGraph_right (l r : Bool) (M : CrossBlock.Matrix) :
    (internalGraph l r M).Adj 2 3 ↔ r = true := by simp [internalGraph, internalAdj]

@[simp] theorem internalGraph_cross (l r : Bool) (M : CrossBlock.Matrix) (a b : Fin 2) :
    (internalGraph l r M).Adj (leftIndex a) (rightIndex b) ↔ M a b = true := by
  fin_cases a <;> fin_cases b <;> simp [internalGraph, internalAdj, leftIndex, rightIndex]

theorem internalGraph_degree_left (l r : Bool) (M : CrossBlock.Matrix) (a : Fin 2) :
    (internalGraph l r M).degree (leftIndex a) =
      (if l then 1 else 0) + CrossBlock.row M a := by
  rw [degree_eq_sum_bits, Fin.sum_univ_four]
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry]
  fin_cases a <;>
    simp [internalGraph, internalAdj, leftIndex] <;> ring_nf

theorem internalGraph_degree_right (l r : Bool) (M : CrossBlock.Matrix) (a : Fin 2) :
    (internalGraph l r M).degree (rightIndex a) =
      (if r then 1 else 0) + CrossBlock.col M a := by
  rw [degree_eq_sum_bits, Fin.sum_univ_four]
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry]
  fin_cases a <;>
    simp [internalGraph, internalAdj, rightIndex] <;> ring_nf

end Problem315.DisjointEncoding

end

end OAI
