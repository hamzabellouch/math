import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedRepresentationEmit
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ParentPrefixSearch

namespace OAI

/-! # Bounded-list prefix restrictions

Forcing one bit scans the ambient indices and retains the resulting list.
This works for every bounded input list, including lists with repetitions;
no finite-set insertion is executed by the prefix controller.
-/

namespace LowSpaceSubsetSum

namespace IndexedMask

variable {n : ℕ}

def insert (i : Fin n) (s : IndexedMask n) : IndexedMask n × ℕ :=
  let out := CountedRepresentationEmit.filterMask (i :: s.indices) (List.finRange n)
  (⟨out.1, by simpa only [List.length_finRange] using
    CountedRepresentationEmit.filterMask_length (i :: s.indices) (List.finRange n)⟩,
    out.2 + n + 3)

theorem insert_value (i : Fin n) (s : IndexedMask n) :
    (insert i s).1.semantic = Insert.insert i s.semantic := by
  ext j
  simp [insert, semantic, CountedRepresentationEmit.filterMask_value]

theorem insert_work (i : Fin n) (s : IndexedMask n) :
    (insert i s).2 ≤ 8 * (n + 1) ^ 2 := by
  have hw := CountedRepresentationEmit.filterMask_work (i :: s.indices) (List.finRange n)
  have hl := s.length_le
  simp only [List.length_cons, List.length_finRange] at hw
  have hm := Nat.mul_le_mul_right n (Nat.add_le_add_right hl 5)
  change _ + n + 3 ≤ _
  nlinarith only [hw, hm, Nat.zero_le n]

end IndexedMask

structure StoredRestriction (n : ℕ) where
  ones : IndexedMask n
  zeros : IndexedMask n

namespace StoredRestriction

variable {n : ℕ}

def semantic (P : StoredRestriction n) : MaskRestriction n :=
  ⟨P.ones.semantic, P.zeros.semantic⟩

def empty : StoredRestriction n := ⟨⟨[], Nat.zero_le _⟩, ⟨[], Nat.zero_le _⟩⟩

theorem empty_value : (empty (n := n)).semantic = MaskRestriction.empty := rfl

def force (P : StoredRestriction n) (i : Fin n) (side : Bool) : StoredRestriction n × ℕ :=
  if side then
    let out := P.ones.insert i
    (⟨out.1, P.zeros⟩, out.2 + 2)
  else
    let out := P.zeros.insert i
    (⟨P.ones, out.1⟩, out.2 + 2)

theorem force_value (P : StoredRestriction n) (i : Fin n) (side : Bool) :
    (P.force i side).1.semantic = P.semantic.force i side := by
  cases side <;> simp only [force, Bool.false_eq_true, ↓reduceIte, semantic,
    MaskRestriction.force, IndexedMask.insert_value]

theorem force_work (P : StoredRestriction n) (i : Fin n) (side : Bool) :
    (P.force i side).2 ≤ 10 * (n + 1) ^ 2 := by
  have ho := IndexedMask.insert_work i P.ones
  have hz := IndexedMask.insert_work i P.zeros
  have hp : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  cases side <;> simp only [force, Bool.false_eq_true, ↓reduceIte] <;> omega

def cells (P : StoredRestriction n) : ℕ :=
  P.ones.indices.length + P.zeros.indices.length + 4

theorem cells_le (P : StoredRestriction n) : P.cells ≤ 2 * n + 4 := by
  have ho := P.ones.length_le
  have hz := P.zeros.length_le
  unfold cells
  omega

end StoredRestriction
end LowSpaceSubsetSum

end OAI
