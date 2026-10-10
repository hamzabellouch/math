import OAI.NumberTheory.Ostmann.Tree.PreorderNodePaths
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveNodeExpansion

namespace OAI

/-! # The actual reconstructed node at a preorder path -/

namespace Ostmann
open scoped Classical

noncomputable def transferNodeAtPath {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → List Bool → ReconstructedTransferNode State
  | 0, σ, t, _ => ⟨σ, t, t, t⟩
  | n + 1, σ, t, [] => ⟨σ, t.1, frequencyRoot n t.2.1, frequencyRoot n t.2.2⟩
  | n + 1, σ, t, b :: path =>
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      if b then transferNodeAtPath sys n (sys.rightState σ P) t.2.2 path
      else transferNodeAtPath sys n (sys.leftState σ P) t.2.1 path

/-- Path lookup and the literal preorder list name the same node. -/
theorem transferNodeList_get_path {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (path : List Bool)
    (hp : path.length < n) (fallback : ReconstructedTransferNode State) :
    (transferNodeList sys n σ t).getD (nodePathIndex n path) fallback =
      transferNodeAtPath sys n σ t path := by
  induction n generalizing σ path with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil => rfl
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hidx := nodePathIndex_lt n path hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · simp only [nodePathIndex, Bool.false_eq_true, ite_false, transferNodeList]
        rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
          List.getD_cons_succ, List.getD_append _ _ _ _ (by
            rw [transferNodeList_length]; exact hidx)]
        exact ih _ _ path hp'
      · simp only [nodePathIndex, ite_true, transferNodeList]
        rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by omega,
          List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
            rw [transferNodeList_length]; omega), transferNodeList_length]
        rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]
        exact ih _ _ path hp'

theorem transferNodeAtPath_valid {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (hv : ValidTransferHistory sys n σ t) (path : List Bool) (hp : path.length < n) :
    (transferNodeAtPath sys n σ t path).Valid sys := by
  apply (validTransferHistory_nodeList_iff sys n σ t).mp hv
  rw [← transferNodeList_get_path sys n σ t path hp (transferNodeAtPath sys n σ t path)]
  rw [List.getD_eq_getElem _ _ (by rw [transferNodeList_length]; exact nodePathIndex_lt n path hp)]
  exact List.getElem_mem _

noncomputable def replayNodeIndices {State : Type*} (sys : TransferHistorySystem State) :
    List Bool → ℕ → (ℕ → ℕ) → State → State
  | [], _, _, σ => σ
  | b :: path, d, p, σ => replayNodeIndices sys path (d + 1) p
      (if b then sys.rightState σ (p d) else sys.leftState σ (p d))

/-- The node's state is obtained by substituting just its proper ancestor
pivots, in their root-to-leaf order. -/
theorem replayNodeIndices_actual {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (path : List Bool)
    (hp : path.length < n) (d : ℕ) (p : ℕ → ℕ)
    (hanc : ∀ k < path.length, p (d + k) =
      (transferNodeAtPath sys n σ t (path.take k)).pivot sys) :
    replayNodeIndices sys path d p σ = (transferNodeAtPath sys n σ t path).state := by
  induction n generalizing σ path d with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil => rfl
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hroot : p d = historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) := by
        simpa only [Nat.add_zero, List.take_zero, transferNodeAtPath,
          ReconstructedTransferNode.pivot] using hanc 0 (by simp)
      cases b
      · simp only [replayNodeIndices, Bool.false_eq_true, ite_false, transferNodeAtPath]
        rw [hroot]
        apply ih _ _ path hp' (d + 1)
        intro k hk
        have hh := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
          transferNodeAtPath, Bool.false_eq_true, ite_false] using hh
      · simp only [replayNodeIndices, ite_true, transferNodeAtPath]
        rw [hroot]
        apply ih _ _ path hp' (d + 1)
        intro k hk
        have hh := hanc (k + 1) (by simpa using Nat.add_lt_add_right hk 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 k, List.take_succ_cons,
          transferNodeAtPath, ite_true] using hh

end Ostmann

end OAI
