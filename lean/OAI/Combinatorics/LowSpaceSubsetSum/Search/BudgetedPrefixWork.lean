import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixController
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorFlow

namespace OAI

namespace LowSpaceSubsetSum.BudgetedPrefixController

open BudgetedSeparatorFlow (Account)
variable {n : ℕ} {I : Instance n} {C : ℕ}

private theorem force_bound (P : StoredRestriction n) (i : Fin n) :
    (P.force i false).2 + (P.force i true).2 + 8 ≤ StoredPrefixController.header n := by
  have h₀ := P.force_work i false
  have h₁ := P.force_work i true
  unfold StoredPrefixController.header
  omega

theorem run_account
    (collect : StoredRestriction n → ℕ → Option (StoredEntry.Dictionary I C × ℕ) × ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (hc : ∀ P b, Account b (collect P b)) (hk : ∀ a b, Account b (check a b))
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) :
    Account budget (run collect check order P budget) := by
  have hh : 8 ≤ StoredPrefixController.header n := by unfold StoredPrefixController.header; omega
  induction order generalizing P budget with
  | nil =>
    rw [run]
    split
    next hb =>
      generalize htdef : collect P (budget - StoredPrefixController.header n) = task
      have htask := hc P (budget - StoredPrefixController.header n)
      rw [htdef] at htask
      cases ht : task.1 with
      | none =>
        simp only [ht, BudgetedSeparatorFlow.Account]
        constructor
        · exact le_trans (Nat.add_le_add_right htask.1 2) (by omega)
        · intro v left h
          contradiction
      | some p =>
        rcases p with ⟨d, left⟩
        have hts := htask.2 d left ht
        simp only [ht, BudgetedSeparatorFlow.Account]
        split
        · constructor
          · dsimp only; omega
          · intro v rest h
            cases h
            dsimp only
            omega
        · have hchecked := hk d.val.records left
          have hw := hchecked.1
          constructor
          · change task.2 + (check d.val.records left).2 + 4 ≤ _
            omega
          · intro v rest h
            have hs := hchecked.2 v rest h
            change rest ≤ budget ∧ task.2 + (check d.val.records left).2 + 4 ≤ budget - rest
            omega
    next _ =>
      constructor
      · dsimp only; omega
      · intro v left h
        contradiction
  | cons i order ih =>
    rw [run]
    split
    next hb =>
      generalize htdef : collect P (budget - StoredPrefixController.header n) = task
      have htask := hc P (budget - StoredPrefixController.header n)
      rw [htdef] at htask
      cases ht : task.1 with
      | none =>
        simp only [ht, BudgetedSeparatorFlow.Account]
        constructor
        · exact le_trans (Nat.add_le_add_right htask.1 2) (by omega)
        · intro v left h
          contradiction
      | some p =>
        rcases p with ⟨d, available⟩
        have hts := htask.2 d available ht
        simp only [ht, BudgetedSeparatorFlow.Account]
        split
        · have hf := force_bound P i
          generalize hldef : run collect check order (P.force i false).1 available = left
          have hl := ih (P.force i false).1 available
          rw [hldef] at hl
          have hlw := hl.1
          cases he : left.1 with
          | none =>
            constructor
            · change task.2 + (P.force i false).2 + left.2 + 6 ≤ _
              omega
            · intro v rest h
              contradiction
          | some p =>
            rcases p with ⟨v, rest⟩
            have hls := hl.2 v rest he
            cases v
            · dsimp only
              generalize hrdef : run collect check order (P.force i true).1 rest = right
              have hr := ih (P.force i true).1 rest
              rw [hrdef] at hr
              have hrw := hr.1
              constructor
              · omega
              · intro v remaining h
                have hrs := hr.2 v remaining h
                change remaining ≤ budget ∧
                  task.2 + (P.force i false).2 + left.2 + (P.force i true).2 + right.2 + 8 ≤ budget - remaining
                omega
            · constructor
              · change task.2 + (P.force i false).2 + left.2 + 6 ≤ _
                omega
              · intro v remaining h
                cases h
                change rest ≤ budget ∧ task.2 + (P.force i false).2 + left.2 + 6 ≤ budget - rest
                omega
        · have hchecked := hk d.val.records available
          have hw := hchecked.1
          constructor
          · change task.2 + (check d.val.records available).2 + 4 ≤ _
            omega
          · intro v rest h
            have hs := hchecked.2 v rest h
            change rest ≤ budget ∧ task.2 + (check d.val.records available).2 + 4 ≤ budget - rest
            omega
    next _ =>
      constructor
      · dsimp only; omega
      · intro v left h
        contradiction

end LowSpaceSubsetSum.BudgetedPrefixController

end OAI
