import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderLaw
import OAI.Combinatorics.TriangleRemoval.Process.Finish

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators
open scoped BigOperators ENNReal Classical

namespace SharpTerminalLeave

def scanList {n : ℕ} (G : Graph n) (as : List (Finset (Fin n))) : Graph n :=
  as.foldl scanAction G

theorem orderLaw_scanList_eq_scanLaw {n : ℕ} (d : ℕ) (G : Graph n)
    (C : Finset (Finset (Fin n))) :
    (orderLaw d C).map (scanList G) = scanLaw d G C := by
  induction d generalizing G C with
  | zero => simp [orderLaw, scanLaw, scanList, PMF.pure_map]
  | succ d ih =>
    by_cases hC : C.Nonempty
    · simp only [orderLaw, scanLaw, dite_eq_left hC, PMF.map_bind, PMF.map_comp]
      congr 1
      funext t
      exact ih (scanAction G t) (C.erase t)
    · simp [orderLaw, scanLaw, hC, scanList, PMF.pure_map]

theorem uniform_order_scan_eq_finish {n : ℕ} (G : Graph n)
    (C : Finset (Finset (Fin n))) (hall : triangles G ⊆ C) :
    (orderLaw C.card C).map (scanList G) = finish G := by
  rw [orderLaw_scanList_eq_scanLaw, scanLaw_eq_finish _ _ _ le_rfl hall]

end SharpTerminalLeave

end

end OAI
