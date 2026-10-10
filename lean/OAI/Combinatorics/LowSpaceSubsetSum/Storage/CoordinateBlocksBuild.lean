import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CoordinateRowBuild

namespace OAI

/-! # Building the four stored separator coordinate rows -/

namespace LowSpaceSubsetSum.CoordinateBlocksBuild

open scoped BigOperators
variable {n g : ℕ}

def run (xs : Fin 4 → List (Fin n)) (hg : ∀ i, (xs i).length = g) :
    (Fin 4 → Vector (Fin n) g) × ℕ :=
  let rows := Vector.ofFn (fun i => CoordinateRowBuild.run (xs i) (hg i))
  (fun i => rows[i.val].1, (∑ i : Fin 4, rows[i.val].2) + 12)

theorem value (xs : Fin 4 → List (Fin n)) (hg : ∀ i, (xs i).length = g)
    (hx : ∀ i, (xs i).Nodup) (S : Fin 4 → Finset (Fin n))
    (hS : ∀ i, (xs i).toFinset = S i) (hcard : ∀ i, (S i).card = g)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (i : Fin 4) (j : Fin g) :
    ((run xs hg).1 i)[j.val] = (TopCoordinates.ofBlocks S hcard hdisj).index (i, j) := by
  simp only [run, Vector.getElem_ofFn, Fin.eta]
  exact CoordinateRowBuild.value (xs i) (hg i) (hx i) (S i) (hS i) (hcard i) j

theorem work (xs : Fin 4 → List (Fin n)) (hg : ∀ i, (xs i).length = g) (hn : g ≤ n) :
    (run xs hg).2 ≤ 80 * (n + 1) ^ 2 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    CoordinateRowBuild.work (xs i) (hg i) hn)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  have hp : 1 ≤ (n + 1) ^ 2 := by nlinarith
  simp only [run, Vector.getElem_ofFn, Fin.eta]
  nlinarith only [h, hp]

end LowSpaceSubsetSum.CoordinateBlocksBuild

end OAI
