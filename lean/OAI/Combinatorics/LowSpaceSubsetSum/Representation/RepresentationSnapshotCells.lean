import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentLiveState

namespace OAI

/-! # Actual mutable-reader cloning scratch

Only the tournament is copied. Both immutable arrays and bounded masks inside
its records are shared. The trace retains the completed left subtree while
copying the right subtree and includes the recursive stack.
-/

namespace LowSpaceSubsetSum.RepresentationSnapshotCells

variable {n : ℕ} {α : Type*}

def copy (N : ℕ) : {d : ℕ} → Tournament.Tree α d → (Tournament.Tree α d × ℕ) × ℕ
  | 0, .leaf v => ((.leaf v, N), N + 8)
  | _d + 1, .node w l r =>
    let a := copy N l
    let b := copy N r
    ((.node w a.1.1 b.1.1, a.1.2 + b.1.2 + N),
      max a.2 (N * (Tournament.nodes l + 1) + b.2 + N + 8))

theorem copy_value (N : ℕ) {d : ℕ} (t : Tournament.Tree α d) :
    (copy N t).1 = Tournament.countedCopy N t := by
  induction t with
  | leaf _ => rfl
  | node w l r ihl ihr => simp only [copy, Tournament.countedCopy, ihl, ihr]

theorem copy_cells (N : ℕ) {d : ℕ} (t : Tournament.Tree α d) :
    (copy N t).2 ≤ 2 * N * 2 ^ (d + 1) + 16 * (d + 1) := by
  induction t with
  | leaf _ => simp only [copy]; norm_num; omega
  | @node d w l r ihl ihr =>
    have he := Tournament.nodes_exact l
    have hp : 1 ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
    have hN := Nat.mul_le_mul_left N hp
    simp only [copy, he, pow_succ, Nat.mul_add, Nat.mul_one]
    simp only [pow_succ, Nat.mul_add, Nat.mul_one] at ihl ihr hN
    apply max_le
    · nlinarith only [ihl, hN]
    · nlinarith only [ihr, hN]

def snapshot (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d) :
    (CountedParentJoin.State I F P mode right d × ℕ) × ℕ :=
  let out := copy (12 * n + 32) s.tree
  have he : out.1.1 = s.tree :=
    (congrArg Prod.fst (copy_value _ s.tree)).trans (Tournament.countedCopy_value _ _)
  ((⟨out.1.1, he.symm ▸ s.valid, he.symm ▸ s.aligned, he.symm ▸ s.sorted⟩, out.1.2), out.2 + 8)

theorem snapshot_value (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d) :
    (snapshot I F P mode right s).1 = CountedParentJoin.snapshot I F P mode right s := by
  simp only [snapshot, CountedParentJoin.snapshot, copy_value]

theorem snapshot_cells (I : Instance n) (F : IndexedMask n) (P : ℤ) (mode : FilteredStream.Mode)
    (right : Array (LeafRecord n)) {d : ℕ} (s : CountedParentJoin.State I F P mode right d)
    (C : ℕ) (hd : d ≤ n) (ht : 2 ^ (d + 1) ≤ 4 * (C + 1)) :
    (snapshot I F P mode right s).2 ≤ 400 * inputScale I * (C + 1) := by
  have h := copy_cells (12 * n + 32) s.tree
  have hu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hc : 12 * n + 32 ≤ 44 * inputScale I := by omega
  have hm := Nat.mul_le_mul hc ht
  change (copy (12 * n + 32) s.tree).2 + 8 ≤ _
  nlinarith only [h, hm, hu, hd]

end LowSpaceSubsetSum.RepresentationSnapshotCells

end OAI
