import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Initial row and column strips of a Young diagram and their cardinalities. -/

namespace ArithmeticTensorSquares.Capacity
open scoped BigOperators

def firstRows (μ : YoungDiagram) (k : Nat) : Finset (Nat × Nat) :=
  μ.cells.filter (fun p => p.1 < k)

def firstCols (μ : YoungDiagram) (k : Nat) : Finset (Nat × Nat) :=
  μ.cells.filter (fun p => p.2 < k)

def rowPrefix (μ : YoungDiagram) (k : Nat) : Nat :=
  ∑ i ∈ Finset.range k, μ.rowLen i

def colPrefix (μ : YoungDiagram) (k : Nat) : Nat :=
  ∑ j ∈ Finset.range k, μ.colLen j

theorem firstRows_card (μ : YoungDiagram) (k : Nat) :
    (firstRows μ k).card = rowPrefix μ k := by
  have h := Finset.sum_card_fiberwise_eq_card_filter μ.cells (Finset.range k) Prod.fst
  simpa only [YoungDiagram.rowLen_eq_card, YoungDiagram.row, rowPrefix,
    firstRows, Finset.mem_range] using h.symm

theorem firstCols_card (μ : YoungDiagram) (k : Nat) :
    (firstCols μ k).card = colPrefix μ k := by
  have h := Finset.sum_card_fiberwise_eq_card_filter μ.cells (Finset.range k) Prod.snd
  simpa only [YoungDiagram.colLen_eq_card, YoungDiagram.col, colPrefix,
    firstCols, Finset.mem_range] using h.symm

end ArithmeticTensorSquares.Capacity

end OAI
