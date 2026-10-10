import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixWork

namespace OAI

namespace LowSpaceSubsetSum.BudgetedPrefixController

variable {n : ℕ} {I : Instance n} {C : ℕ}

/-- Full-tree analysis allowance; the executable never evaluates it. -/
def allowance (collect : StoredRestriction n → StoredEntry.Dictionary I C)
    (collectBill : StoredRestriction n → ℕ) (checkBill : Array (StoredEntry n) → ℕ) :
    List (Fin n) → StoredRestriction n → ℕ
  | order, P =>
    StoredPrefixController.header n + collectBill P +
    if (collect P).val.keys.overflow then
      match order with
      | [] => 0
      | i :: rest => allowance collect collectBill checkBill rest (P.force i false).1 +
          allowance collect collectBill checkBill rest (P.force i true).1
    else checkBill (collect P).val.records

theorem run_remaining
    (collect : StoredRestriction n → ℕ → Option (StoredEntry.Dictionary I C × ℕ) × ℕ)
    (pureCollect : StoredRestriction n → StoredEntry.Dictionary I C)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (collectBill : StoredRestriction n → ℕ) (checkBill : Array (StoredEntry n) → ℕ)
    (hc : ∀ P b d left, (collect P b).1 = some (d, left) → d = pureCollect P ∧ b ≤ left + collectBill P)
    (hk : ∀ a b v left, (check a b).1 = some (v, left) → b ≤ left + checkBill a)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) (v : Bool) (remaining : ℕ)
    (h : (run collect check order P budget).1 = some (v, remaining)) :
    budget ≤ remaining + allowance pureCollect collectBill checkBill order P := by
  induction order generalizing P budget v remaining with
  | nil =>
    rw [run] at h
    split at h
    next hb =>
      cases ht : (collect P (budget - StoredPrefixController.header n)).1 with
      | none => simp only [ht] at h; contradiction
      | some p =>
        rcases p with ⟨d, left⟩
        have hv := hc P _ d left ht
        simp only [ht] at h
        split at h
        next ho =>
          cases h
          simp only [allowance, ← hv.1, ho, ↓reduceIte]
          omega
        next ho =>
          have hs := hk d.val.records left v remaining h
          simp only [allowance, ← hv.1, ho, Bool.false_eq_true, ↓reduceIte]
          omega
    next _ => contradiction
  | cons i order ih =>
    rw [run] at h
    split at h
    next hb =>
      cases ht : (collect P (budget - StoredPrefixController.header n)).1 with
      | none => simp only [ht] at h; contradiction
      | some p =>
        rcases p with ⟨d, left⟩
        have hv := hc P _ d left ht
        simp only [ht] at h
        split at h
        next ho =>
          cases hl : (run collect check order (P.force i false).1 left).1 with
          | none => simp only [hl] at h; contradiction
          | some p =>
            rcases p with ⟨lv, lb⟩
            have hleft := ih (P.force i false).1 left lv lb hl
            cases lv
            · simp only [hl] at h
              have hright := ih (P.force i true).1 lb v remaining h
              simp only [allowance, ← hv.1, ho, ↓reduceIte]
              omega
            · simp only [hl] at h
              cases h
              simp only [allowance, ← hv.1, ho, ↓reduceIte]
              omega
        next ho =>
          have hs := hk d.val.records left v remaining h
          simp only [allowance, ← hv.1, ho, Bool.false_eq_true, ↓reduceIte]
          omega
    next _ => contradiction

end LowSpaceSubsetSum.BudgetedPrefixController

end OAI
