import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixAllowance

namespace OAI

namespace LowSpaceSubsetSum.BudgetedPrefixController

variable {n : ℕ} {I : Instance n} {C : ℕ}

/-- Paying the full source-prefix ledger guarantees that early-YES execution
finishes; the allowance does not have to be computed at runtime. -/
theorem run_complete
    (collect : StoredRestriction n → ℕ → Option (StoredEntry.Dictionary I C × ℕ) × ℕ)
    (pureCollect : StoredRestriction n → StoredEntry.Dictionary I C)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (collectBill : StoredRestriction n → ℕ) (checkBill : Array (StoredEntry n) → ℕ)
    (hc : ∀ P b, collectBill P ≤ b → ∃ left, (collect P b).1 = some (pureCollect P, left))
    (hcr : ∀ P b d left, (collect P b).1 = some (d, left) → d = pureCollect P ∧ b ≤ left + collectBill P)
    (hk : ∀ a b, checkBill a ≤ b → ∃ v left, (check a b).1 = some (v, left))
    (hkr : ∀ a b v left, (check a b).1 = some (v, left) → b ≤ left + checkBill a)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ)
    (hb : allowance pureCollect collectBill checkBill order P ≤ budget) :
    ∃ v left, (run collect check order P budget).1 = some (v, left) := by
  induction order generalizing P budget with
  | nil =>
    have hhead : StoredPrefixController.header n ≤ budget := by
      unfold allowance at hb
      split at hb <;> omega
    have hbill : collectBill P ≤ budget - StoredPrefixController.header n := by
      unfold allowance at hb
      split at hb <;> omega
    obtain ⟨left, hcollect⟩ := hc P (budget - StoredPrefixController.header n) hbill
    have hr := (hcr P _ _ _ hcollect).2
    by_cases ho : (pureCollect P).val.keys.overflow = true
    · exact ⟨false, left, by rw [run, ite_eq_left hhead]; simp only [↓reduceIte, hcollect, ho]⟩
    · have hcheck : checkBill (pureCollect P).val.records ≤ left := by
        simp only [allowance, ho, Bool.false_eq_true, ↓reduceIte] at hb
        omega
      obtain ⟨v, rest, hchecked⟩ := hk (pureCollect P).val.records left hcheck
      exact ⟨v, rest, by rw [run, ite_eq_left hhead]; simp only [↓reduceIte, hcollect, ho, Bool.false_eq_true, hchecked]⟩
  | cons i order ih =>
    have hhead : StoredPrefixController.header n ≤ budget := by
      unfold allowance at hb
      split at hb <;> omega
    have hbill : collectBill P ≤ budget - StoredPrefixController.header n := by
      unfold allowance at hb
      split at hb <;> omega
    obtain ⟨left, hcollect⟩ := hc P (budget - StoredPrefixController.header n) hbill
    have hr := (hcr P _ _ _ hcollect).2
    by_cases ho : (pureCollect P).val.keys.overflow = true
    · have hsum : allowance pureCollect collectBill checkBill order (P.force i false).1 +
          allowance pureCollect collectBill checkBill order (P.force i true).1 ≤ left := by
        simp only [allowance, ho, ↓reduceIte] at hb
        omega
      obtain ⟨v, rest, hl⟩ := ih (P.force i false).1 left (by omega)
      have hleft := run_remaining collect pureCollect check collectBill checkBill hcr hkr
        order (P.force i false).1 left v rest hl
      cases v
      · obtain ⟨v', finalBudget, hright⟩ := ih (P.force i true).1 rest (by omega)
        exact ⟨v', finalBudget, by rw [run, ite_eq_left hhead]; simp only [↓reduceIte, hcollect, ho, hl, hright]⟩
      · exact ⟨true, rest, by rw [run, ite_eq_left hhead]; simp only [↓reduceIte, hcollect, ho, hl]⟩
    · have hcheck : checkBill (pureCollect P).val.records ≤ left := by
        simp only [allowance, ho, Bool.false_eq_true, ↓reduceIte] at hb
        omega
      obtain ⟨v, rest, hchecked⟩ := hk (pureCollect P).val.records left hcheck
      exact ⟨v, rest, by rw [run, ite_eq_left hhead]; simp only [↓reduceIte, hcollect, ho, Bool.false_eq_true, hchecked]⟩

end LowSpaceSubsetSum.BudgetedPrefixController

end OAI
