import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalBackground
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredBackgroundBlocks
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationAllocationExecution

namespace OAI

/-! # Materializing the eight allocated background lists

The outside domain is scanned and sorted, the six binomial widths determine
the eight sizes, and the consecutive rows are copied from that domain. The
size check makes every array access valid on every input execution.
-/

namespace LowSpaceSubsetSum.RepresentationBackgroundPreparation

open scoped BigOperators
variable {n : ℕ}

def run (_I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3) :
    Option (Vector (List (Fin n)) 8) × ℕ :=
  let outside := CanonicalBackground.run v
  let counts := RepresentationAllocationExecution.run n guesses
  if h : (∑ i : Fin 8, counts.1[i.val]) = outside.1.length then
    let xs : Vector (Fin n) outside.1.length := ⟨outside.1.toArray, by simp only [List.size_toArray]⟩
    let rows := StoredBackgroundBlocks.run xs counts.1 h
    (some rows.1, outside.2 + counts.2 + rows.2 + 20)
  else (none, outside.2 + counts.2 + 20)

theorem run_of_size (I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3)
    (h : (∑ i : Fin 8, (RepresentationAllocationExecution.run n guesses).1[i.val]) =
      (CanonicalBackground.run v).1.length) :
    (run I v guesses).1 = some
      (StoredBackgroundBlocks.run
        (⟨(CanonicalBackground.run v).1.toArray, by simp only [List.size_toArray]⟩)
        (RepresentationAllocationExecution.run n guesses).1 h).1 := by
  unfold run
  dsimp only
  rw [dite_eq_left h]

theorem work (I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3) :
    (run I v guesses).2 ≤ 1000 * (n + 1) ^ 2 := by
  have ho := CanonicalBackground.work v
  have hl := CanonicalBackground.length_le v
  have hc := RepresentationAllocationExecution.work n guesses
  unfold run
  dsimp only
  split
  · change (CanonicalBackground.run v).2 +
      (RepresentationAllocationExecution.run n guesses).2 +
      (32 * (CanonicalBackground.run v).1.length + 200) + 20 ≤ _
    nlinarith only [ho, hl, hc, Nat.zero_le (n ^ 2)]
  · change (CanonicalBackground.run v).2 +
      (RepresentationAllocationExecution.run n guesses).2 + 20 ≤ _
    nlinarith only [ho, hc, Nat.zero_le (n ^ 2)]

theorem lengths (I : Instance n) (v : Vector (Fin n) n) (guesses : Vector ℕ 3)
    (rows : Vector (List (Fin n)) 8) (h : (run I v guesses).1 = some rows)
    (j : Fin 8) : rows[j.val].length ≤ n := by
  have hout := CanonicalBackground.length_le v
  unfold run at h
  dsimp only at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    subst rows
    simp only [StoredBackgroundBlocks.run, Vector.getElem_ofFn,
      StoredBackgroundBlocks.row_length]
    have hj := Finset.single_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin 8))) =>
        Nat.zero_le (RepresentationAllocationExecution.run n guesses).1[i.val])
      (Finset.mem_univ j)
    exact hj.trans (hc.le.trans hout)
  next hc => simp only [reduceCtorEq] at h

end LowSpaceSubsetSum.RepresentationBackgroundPreparation

end OAI
