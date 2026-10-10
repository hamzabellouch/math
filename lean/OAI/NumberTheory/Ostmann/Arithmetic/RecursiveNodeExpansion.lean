import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveLeafExpansion

namespace OAI

/-! # The exact preorder list of reconstructed arithmetic tests -/

namespace Ostmann

open scoped Classical

structure ReconstructedTransferNode (State : Type*) where
  state : State
  root : ℤ
  left : ℤ
  right : ℤ

namespace ReconstructedTransferNode

noncomputable def pivot {State : Type*} (sys : TransferHistorySystem State)
    (node : ReconstructedTransferNode State) : ℕ :=
  historyPivot sys node.state node.root node.left node.right

def Valid {State : Type*} (sys : TransferHistorySystem State)
    (node : ReconstructedTransferNode State) : Prop :=
  ValidTransferNode sys node.state node.root node.left node.right (node.pivot sys)

end ReconstructedTransferNode

noncomputable def transferNodeList {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → List (ReconstructedTransferNode State)
  | 0, _, _ => []
  | n + 1, σ, t =>
      let node : ReconstructedTransferNode State :=
        ⟨σ, t.1, frequencyRoot n t.2.1, frequencyRoot n t.2.2⟩
      node :: (transferNodeList sys n (sys.leftState σ (node.pivot sys)) t.2.1 ++
        transferNodeList sys n (sys.rightState σ (node.pivot sys)) t.2.2)

theorem transferNodeList_length {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    (transferNodeList sys n σ t).length = 2 ^ n - 1 := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [transferNodeList, List.length_cons, List.length_append, ih]
    have h := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

/-- The pivot witness in the original definition is precisely the integer
reconstruction, so no existential choice changes the child states. -/
theorem validTransferHistory_reconstructed_iff {State : Type*}
    (sys : TransferHistorySystem State) (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) :
    ValidTransferHistory sys (n + 1) σ t ↔
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P ∧
        ValidTransferHistory sys n (sys.leftState σ P) t.2.1 ∧
        ValidTransferHistory sys n (sys.rightState σ P) t.2.2 := by
  constructor
  · rintro ⟨P, hp, hl, hr⟩
    rw [hp.historyPivot_eq]
    exact ⟨hp, hl, hr⟩
  · rintro ⟨hp, hl, hr⟩
    exact ⟨_, hp, hl, hr⟩

/-- All arithmetic support conditions in a complete history are the tests
of its explicitly reconstructed preorder node list. -/
theorem validTransferHistory_nodeList_iff {State : Type*}
    (sys : TransferHistorySystem State) (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    ValidTransferHistory sys n σ t ↔ ∀ node ∈ transferNodeList sys n σ t, node.Valid sys := by
  induction n generalizing σ with
  | zero => simp [ValidTransferHistory, transferNodeList]
  | succ n ih =>
    rw [validTransferHistory_reconstructed_iff]
    simp only [transferNodeList, List.mem_cons, List.mem_append, or_imp,
      forall_and, forall_eq, ← ih]
    rfl

end Ostmann

end OAI
