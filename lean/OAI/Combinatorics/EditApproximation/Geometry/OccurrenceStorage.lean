import OAI.Combinatorics.EditApproximation.Geometry.OccurrenceIndex
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoStorage
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace PositionCounts

/-- All counters allocated in the position trie are bounded. -/
def CountsLE (C : ℕ) : PositionCounts → Prop
  | .empty => True
  | .node n l r => n ≤ C ∧ CountsLE C l ∧ CountsLE C r

theorem CountsLE.mono {C D : ℕ} (hCD : C ≤ D) {tree : PositionCounts}
    (h : tree.CountsLE C) : tree.CountsLE D := by
  induction tree with
  | empty => trivial
  | node n l r ihl ihr => exact ⟨h.1.trans hCD, ihl h.2.1, ihr h.2.2⟩

theorem CountsLE.count {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) :
    tree.count ≤ C := by
  cases tree with
  | empty => exact Nat.zero_le _
  | node n l r => exact h.1

theorem CountsLE.left {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) :
    tree.left.CountsLE C := by
  cases tree with
  | empty => trivial
  | node n l r => exact h.2.1

theorem CountsLE.right {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) :
    tree.right.CountsLE C := by
  cases tree with
  | empty => trivial
  | node n l r => exact h.2.2

theorem CountsLE.add {C : ℕ} {tree : PositionCounts} (h : tree.CountsLE C) (d i : ℕ) :
    (tree.add d i).CountsLE (C + 1) := by
  induction d generalizing tree i with
  | zero => exact ⟨Nat.add_le_add_right h.count 1,
      h.left.mono (Nat.le_succ _), h.right.mono (Nat.le_succ _)⟩
  | succ d ih =>
    simp only [PositionCounts.add]
    split
    · exact ⟨Nat.add_le_add_right h.count 1, ih h.left _, h.right.mono (Nat.le_succ _)⟩
    · exact ⟨Nat.add_le_add_right h.count 1, h.left.mono (Nat.le_succ _), ih h.right _⟩

/-- A tag, two child pointers, and the binary counter at each allocated node. -/


theorem storageBits_le {tree : PositionCounts} {C : ℕ} (h : tree.CountsLE C) :
    tree.storageBits ≤ (Nat.size C + 3) * tree.nodes := by
  induction tree with
  | empty => simp only [storageBits, nodes, Nat.mul_zero, le_refl]
  | node n l r ihl ihr =>
    have hn := Nat.size_le_size h.1
    have hl := ihl h.2.1
    have hr := ihr h.2.2
    simp only [storageBits, nodes]
    nlinarith only [hn, hl, hr]

end PositionCounts
namespace BinaryMemo

/-- Concrete trie storage with the supplied stored-value representation. -/


theorem valueStorage_le {α : Type*} (bits : α → ℕ) (W : ℕ) (memory : BinaryMemo α)
    (h : AllValues (fun a => bits a ≤ W) memory) :
    valueStorage bits memory ≤ (W + 3) * memory.nodes := by
  induction memory with
  | empty => simp only [valueStorage, nodes, Nat.mul_zero, le_refl]
  | node value l r ihl ihr =>
    have hl : AllValues (fun a => bits a ≤ W) l := fun key a ha => h (false :: key) a ha
    have hr : AllValues (fun a => bits a ≤ W) r := fun key a ha => h (true :: key) a ha
    have hv : (value.map bits).getD 0 ≤ W := by
      cases value with
      | none => exact Nat.zero_le _
      | some a => exact h [] a rfl
    have hls := ihl hl
    have hrs := ihr hr
    simp only [valueStorage, nodes]
    nlinarith only [hv, hls, hrs]

end BinaryMemo

theorem occurrenceBuild_nodes (s p : ℕ) (entries : List (ℕ × ℕ)) :
    (occurrenceBuild s p entries).nodes ≤ entries.length * (s + 1) := by
  induction entries with
  | nil => simp only [occurrenceBuild, BinaryMemo.nodes, List.length_nil, Nat.zero_mul, le_refl]
  | cons e es ih =>
    have h := BinaryMemo.insert_nodes (occurrenceBuild s p es) (binaryMemoKey s e.1)
      (((occurrenceBuild s p es).lookup (binaryMemoKey s e.1)).getD .empty |>.add p e.2)
    simp only [binaryMemoKey_length] at h
    simp only [occurrenceBuild, List.length_cons]
    nlinarith only [h, ih]

theorem occurrenceBuild_values (s p : ℕ) (entries : List (ℕ × ℕ)) :
    BinaryMemo.AllValues (fun tree : PositionCounts =>
      tree.CountsLE entries.length ∧ tree.nodes ≤ entries.length * (p + 1))
      (occurrenceBuild s p entries) := by
  induction entries with
  | nil => exact BinaryMemo.allValues_empty _
  | cons e es ih =>
    have hold : let tree := ((occurrenceBuild s p es).lookup (binaryMemoKey s e.1)).getD .empty
        tree.CountsLE es.length ∧ tree.nodes ≤ es.length * (p + 1) := by
      cases hfind : (occurrenceBuild s p es).lookup (binaryMemoKey s e.1) with
      | none => simp only [Option.getD_none, PositionCounts.CountsLE, PositionCounts.nodes]; exact ⟨trivial, Nat.zero_le _⟩
      | some tree => exact ih _ _ hfind
    apply BinaryMemo.AllValues.insert
    · intro key tree htree
      obtain ⟨hc, hn⟩ := ih key tree htree
      exact ⟨hc.mono (by simp), hn.trans (Nat.mul_le_mul_right _ (by simp))⟩
    · refine ⟨hold.1.add p e.2, ?_⟩
      have hn := PositionCounts.add_nodes
        (((occurrenceBuild s p es).lookup (binaryMemoKey s e.1)).getD .empty) p e.2
      have ho := hold.2
      simp only [List.length_cons]
      nlinarith only [hn, ho]

theorem occurrenceBuild_storage (s p : ℕ) (entries : List (ℕ × ℕ)) :
    BinaryMemo.valueStorage PositionCounts.storageBits (occurrenceBuild s p entries) ≤
      ((Nat.size entries.length + 3) * (entries.length * (p + 1)) + 3) *
        (entries.length * (s + 1)) := by
  have hv := occurrenceBuild_values s p entries
  apply (BinaryMemo.valueStorage_le _ _ _ (fun key tree htree =>
    (PositionCounts.storageBits_le (hv key tree htree).1).trans
      (Nat.mul_le_mul_left _ (hv key tree htree).2))).trans
  exact Nat.mul_le_mul_left _ (occurrenceBuild_nodes s p entries)

end EditApproximation

end OAI
