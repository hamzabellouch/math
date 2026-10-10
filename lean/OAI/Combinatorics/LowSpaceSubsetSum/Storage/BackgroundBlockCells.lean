import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredBackgroundBlocks

namespace OAI

/-! # Copying the eight background rows from their shared array

Each read uses the computed prefix-sum offset. Rows are retained once in an
explicit vector, and the returned view indexes that vector.
-/

namespace LowSpaceSubsetSum.BackgroundBlockCells

open scoped BigOperators
variable {n m : ℕ}

def index (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = m)
    (i : Fin 8) (k : Fin counts[i.val]) : Fin m :=
  ⟨(∑ j : Fin i.val, counts[(Fin.castLE i.isLt.le j).val])+k.val, by
    have h := (StoredBackgroundBlocks.index counts hc i k).isLt
    rwa [StoredBackgroundBlocks.index_value] at h⟩

theorem index_value (counts : Vector ℕ 8) (hc : (∑ i : Fin 8, counts[i.val]) = m)
    (i : Fin 8) (k : Fin counts[i.val]) :
    index counts hc i k = StoredBackgroundBlocks.index counts hc i k := by
  apply Fin.ext
  exact (StoredBackgroundBlocks.index_value counts hc i k).symm

def row (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) (i : Fin 8) :
    (List (Fin n) × ℕ) × ℕ :=
  let out := (List.finRange counts[i.val]).map (fun k => xs[(index counts hc i k).val])
  ((out, 24*counts[i.val]+16), 6*counts[i.val]+32)

theorem row_value (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) (i : Fin 8) :
    (row xs counts hc i).1.1 = StoredBackgroundBlocks.row xs counts hc i := by
  simp only [row, StoredBackgroundBlocks.row, List.ofFn_eq_map, index_value]

def run (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) :
    (Vector (List (Fin n)) 8 × ℕ) × ℕ :=
  let rows := Vector.ofFn (fun i => row xs counts hc i)
  ((rows.map (fun r => r.1.1), 32*m+200),
    (∑ i : Fin 8, rows[i.val].2)+4*m+128)

theorem value (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) :
    (run xs counts hc).1 = StoredBackgroundBlocks.run xs counts hc := by
  apply Prod.ext
  · apply Vector.ext
    intro i hi
    simp only [run, StoredBackgroundBlocks.run, Vector.getElem_map, Vector.getElem_ofFn, row_value]
  · rfl

theorem row_work (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) :
    (∑ i : Fin 8, (row xs counts hc i).1.2)+72 ≤ (run xs counts hc).1.2 := by
  simp only [row, run, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hc]
  omega

theorem cells (xs : Vector (Fin n) m) (counts : Vector ℕ 8)
    (hc : (∑ i : Fin 8, counts[i.val]) = m) :
    (run xs counts hc).2 ≤ 16*m+512 := by
  simp only [run, Vector.getElem_ofFn, row, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, hc]
  omega

end LowSpaceSubsetSum.BackgroundBlockCells

end OAI
