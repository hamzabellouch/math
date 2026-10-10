import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationWeightedReader

namespace OAI

/-! # Measured construction of the row tournament

Each leaf calls its measured initializer once; each internal node evaluates
its two candidate keys. Binary paths are converted to array indices by an
explicit recursive computation. No row array is constructed by this routine.
-/

namespace LowSpaceSubsetSum

namespace Tournament

variable {α : Type*}

def measuredBuild (key : α → ℤ × ℕ) : (d : ℕ) →
    ((Fin d → Bool) → Option α × ℕ) → Tree α d × ℕ
  | 0, front =>
    let x := front Fin.elim0
    (.leaf x.1, x.2 + 1)
  | d + 1, front =>
    let l := measuredBuild key d (fun p => front (Fin.cons false p))
    let r := measuredBuild key d (fun p => front (Fin.cons true p))
    let w := measuredPick key (winner l.1) (winner r.1)
    (.node w.1 l.1 r.1, l.2 + r.2 + w.2 + 5)

theorem measuredBuild_value (key : α → ℤ × ℕ) (d : ℕ)
    (front : (Fin d → Bool) → Option α × ℕ) :
    (measuredBuild key d front).1 = build (fun x => (key x).1) d (fun p => (front p).1) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [measuredBuild, build, measuredPick_value, ih, node]

theorem measuredBuild_work (key : α → ℤ × ℕ) (K R : ℕ)
    (hk : ∀ x, (key x).2 ≤ K) (d : ℕ)
    (front : (Fin d → Bool) → Option α × ℕ) (hf : ∀ p, (front p).2 ≤ R) :
    (measuredBuild key d front).2 ≤ (R + 2 * K + 9) * 2 ^ d - (2 * K + 8) := by
  induction d with
  | zero => simp only [measuredBuild, pow_zero, Nat.mul_one]; have := hf Fin.elim0; omega
  | succ d ih =>
    have hl := ih (fun p => front (Fin.cons false p)) (fun p => hf _)
    have hr := ih (fun p => front (Fin.cons true p)) (fun p => hf _)
    have hp := measuredPick_work key K hk
      (winner (measuredBuild key d (fun p => front (Fin.cons false p))).1)
      (winner (measuredBuild key d (fun p => front (Fin.cons true p))).1)
    have hpow : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by decide)
    have hbase : 2 * K + 8 ≤ (R + 2 * K + 9) * 2 ^ d := by nlinarith
    simp only [measuredBuild, pow_succ, ← Nat.mul_assoc]
    omega

end Tournament

namespace PaddedRows

/-- Little-endian binary evaluation. The cost includes access to a bit in a
path built by at most `d` nested `Fin.cons` nodes. -/
def measuredIndex : (d : ℕ) → (RowMerge.Path d) → ℕ × ℕ
  | 0, _ => (0, 1)
  | d + 1, p =>
    let t := measuredIndex d (fun i => p i.succ)
    ((if p 0 then 1 else 0) + 2 * t.1, t.2 + 2 * d + 6)

private theorem index_sum (d : ℕ) (p : RowMerge.Path d) :
    (index d p).val = ∑ i : Fin d, (if p i then 1 else 0) * 2 ^ i.val := by
  change (∑ i : Fin d, (finTwoEquiv.symm (p i)).val * 2 ^ i.val) = _
  apply Finset.sum_congr rfl
  intro i _
  cases h : p i <;> rfl

theorem measuredIndex_value (d : ℕ) (p : RowMerge.Path d) :
    (measuredIndex d p).1 = (index d p).val := by
  induction d with
  | zero => simp [measuredIndex]
  | succ d ih =>
    rw [index_sum, Fin.sum_univ_succ]
    simp only [measuredIndex, ih, index_sum, Fin.val_zero, pow_zero, Nat.mul_one,
      Fin.val_succ, pow_succ']
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem measuredIndex_work (d : ℕ) (p : RowMerge.Path d) :
    (measuredIndex d p).2 ≤ 4 * (d + 1) ^ 2 := by
  induction d with
  | zero => norm_num [measuredIndex]
  | succ d ih =>
    have h := ih (fun i => p i.succ)
    change _ + 2 * d + 6 ≤ _
    nlinarith

end PaddedRows
end LowSpaceSubsetSum

namespace LowSpaceSubsetSum.FilteredStream

variable {α β : Type*}

/-- Initialize and read one padded row, directly from the shared arrays. -/
def measuredFront (left : Array α) (right : Array β)
    (row : α → PairCursor.State α right.size × ℕ) (d : ℕ) (p : RowMerge.Path d) :
    Option (RowMerge.Front d (α × β) (Cursor (α := α) right)) × ℕ :=
  let i := PaddedRows.measuredIndex d p
  if h : i.1 < left.size then
    let r := row left[i.1]
    let q := countedRead right (some r.1)
    (q.1.map (fun z => ⟨p, z.1, z.2⟩), i.2 + r.2 + q.2 + 6)
  else (none, i.2 + 2)

theorem measuredFront_value (left : Array α) (right : Array β)
    (row : α → PairCursor.State α right.size × ℕ) (d : ℕ) (p : RowMerge.Path d) :
    (measuredFront left right row d p).1 =
      RowMerge.front (read right) p
        (PaddedRows.rows (left.map (fun x => (row x).1)) d p) := by
  simp only [measuredFront, PaddedRows.measuredIndex_value, PaddedRows.rows,
    Array.size_map, RowMerge.front]
  split_ifs with h
  · simp only [Array.getElem_map, countedRead_value]
  · rfl

theorem measuredFront_work (left : Array α) (right : Array β)
    (row : α → PairCursor.State α right.size × ℕ) (R : ℕ)
    (hr : ∀ x, (row x).2 ≤ R) (d : ℕ) (p : RowMerge.Path d) :
    (measuredFront left right row d p).2 ≤ 4 * (d + 1) ^ 2 + R + 30 := by
  have hi := PaddedRows.measuredIndex_work d p
  unfold measuredFront
  dsimp only
  split
  · have hr' := hr left[(PaddedRows.measuredIndex d p).1]
    have hq := countedRead_work right (some (row left[(PaddedRows.measuredIndex d p).1]).1)
    dsimp only
    omega
  · dsimp only
    omega

def measuredInitialTree (left : Array α) (right : Array β) (key : α × β → ℤ × ℕ)
    (row : α → PairCursor.State α right.size × ℕ) (d : ℕ) :=
  Tournament.measuredBuild
    (fun x : RowMerge.Front d (α × β) (Cursor (α := α) right) => key x.value)
    d (measuredFront left right row d)

theorem measuredInitialTree_value (left : Array α) (right : Array β)
    (key : α × β → ℤ × ℕ) (row : α → PairCursor.State α right.size × ℕ) (d : ℕ) :
    (measuredInitialTree left right key row d).1 =
      RowMerge.start (fun x => (key x).1) (read right)
        (PaddedRows.rows (left.map (fun x => (row x).1)) d) := by
  simp only [measuredInitialTree, Tournament.measuredBuild_value, RowMerge.start]
  congr 1
  funext p
  exact measuredFront_value left right row d p

theorem measuredInitialTree_work (left : Array α) (right : Array β)
    (key : α × β → ℤ × ℕ) (row : α → PairCursor.State α right.size × ℕ)
    (K R : ℕ) (hk : ∀ x, (key x).2 ≤ K) (hr : ∀ x, (row x).2 ≤ R) (d : ℕ) :
    (measuredInitialTree left right key row d).2 ≤
      (4 * (d + 1) ^ 2 + R + 2 * K + 39) * 2 ^ d := by
  have h := Tournament.measuredBuild_work (fun x => key x.value) K
    (4 * (d + 1) ^ 2 + R + 30) (fun x => hk x.value) d
    (measuredFront left right row d) (measuredFront_work left right row R hr d)
  calc
    _ ≤ (4 * (d + 1) ^ 2 + R + 30 + 2 * K + 9) * 2 ^ d - (2 * K + 8) := h
    _ ≤ (4 * (d + 1) ^ 2 + R + 30 + 2 * K + 9) * 2 ^ d := Nat.sub_le _ _
    _ = _ := by ring

end LowSpaceSubsetSum.FilteredStream

end OAI
