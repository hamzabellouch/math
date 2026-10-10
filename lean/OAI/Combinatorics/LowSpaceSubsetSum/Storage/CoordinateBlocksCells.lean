import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CoordinateRowCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CoordinateBlocksBuild

namespace OAI

/-! # Four coordinate sorts with previously completed rows retained -/

namespace LowSpaceSubsetSum.CoordinateBlocksCells

open scoped BigOperators
variable {n g : ℕ}

def run (xs : Fin 4 → List (Fin n)) (hg : ∀ i, (xs i).length = g) :
    ((Fin 4 → Vector (Fin n) g) × ℕ) × ℕ :=
  let rows := Vector.ofFn (fun i => CoordinateRowCells.run (xs i) (hg i))
  ((fun i => rows[i.val].1.1, (∑ i : Fin 4, rows[i.val].1.2)+12),
    (∑ i : Fin 4, rows[i.val].2)+8*(n+1))

theorem value (xs : Fin 4 → List (Fin n)) (hg : ∀ i, (xs i).length = g) :
    (run xs hg).1 = CoordinateBlocksBuild.run xs hg := by
  simp only [run, CoordinateBlocksBuild.run, Vector.getElem_ofFn, CoordinateRowCells.value]

theorem cells (xs : Fin 4 → List (Fin n)) (hg : ∀ i, (xs i).length = g) (hn : g ≤ n) :
    (run xs hg).2 ≤ 400*(n+1)^2 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    CoordinateRowCells.cells (xs i) (hg i) hn)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  simp only [run, Vector.getElem_ofFn]
  nlinarith only [h, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.CoordinateBlocksCells

end OAI
