import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredPrefixController

namespace OAI

/-! # Stored-prefix traversal with one shared execution budget -/

namespace LowSpaceSubsetSum.BudgetedPrefixController

variable {n : ℕ} {I : Instance n} {C : ℕ}

def run
    (collect : StoredRestriction n → ℕ → Option (StoredEntry.Dictionary I C × ℕ) × ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ) :
    List (Fin n) → StoredRestriction n → ℕ → Option (Bool × ℕ) × ℕ
  | order, P, budget =>
    if StoredPrefixController.header n ≤ budget then
      let task := collect P (budget - StoredPrefixController.header n)
      match task.1 with
      | none => (none, task.2 + 2)
      | some (dictionary, available) =>
        if dictionary.val.keys.overflow then
          match order with
          | [] => (some (false, available), task.2 + 4)
          | i :: rest =>
            let p₀ := P.force i false
            let left := run collect check rest p₀.1 available
            match left.1 with
            | none => (none, task.2 + p₀.2 + left.2 + 6)
            | some (true, remaining) => (some (true, remaining), task.2 + p₀.2 + left.2 + 6)
            | some (false, remaining) =>
              let p₁ := P.force i true
              let right := run collect check rest p₁.1 remaining
              (right.1, task.2 + p₀.2 + left.2 + p₁.2 + right.2 + 8)
        else
          let checked := check dictionary.val.records available
          (checked.1, task.2 + checked.2 + 4)
    else (none, 1)

theorem run_value
    (collect : StoredRestriction n → ℕ → Option (StoredEntry.Dictionary I C × ℕ) × ℕ)
    (pureCollect : StoredRestriction n → StoredEntry.Dictionary I C × ℕ)
    (check : Array (StoredEntry n) → ℕ → Option (Bool × ℕ) × ℕ)
    (pureCheck : Array (StoredEntry n) → Bool × ℕ)
    (hc : ∀ P b d left, (collect P b).1 = some (d, left) → d = (pureCollect P).1 ∧ left ≤ b)
    (hk : ∀ a b v left, (check a b).1 = some (v, left) → v = (pureCheck a).1 ∧ left ≤ b)
    (order : List (Fin n)) (P : StoredRestriction n) (budget : ℕ) (v : Bool) (remaining : ℕ)
    (h : (run collect check order P budget).1 = some (v, remaining)) :
    v = (StoredPrefixController.run pureCollect pureCheck order P).1 ∧ remaining ≤ budget := by
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
          exact ⟨by simp only [StoredPrefixController.run, ← hv.1, ho, ↓reduceIte],
            hv.2.trans (Nat.sub_le _ _)⟩
        next ho =>
          have hv' := hk d.val.records left v remaining h
          exact ⟨by simpa only [StoredPrefixController.run, ← hv.1, ho, Bool.false_eq_true, ↓reduceIte] using hv'.1,
            hv'.2.trans (hv.2.trans (Nat.sub_le _ _))⟩
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
              exact ⟨by simp only [StoredPrefixController.run, ← hv.1, ho, ↓reduceIte, ← hleft.1,
                Bool.false_eq_true]; exact hright.1,
                hright.2.trans (hleft.2.trans (hv.2.trans (Nat.sub_le _ _)))⟩
            · simp only [hl] at h
              cases h
              exact ⟨by simp only [StoredPrefixController.run, ← hv.1, ho, ↓reduceIte, ← hleft.1],
                hleft.2.trans (hv.2.trans (Nat.sub_le _ _))⟩
        next ho =>
          have hv' := hk d.val.records left v remaining h
          exact ⟨by simpa only [StoredPrefixController.run, ← hv.1, ho, Bool.false_eq_true, ↓reduceIte] using hv'.1,
            hv'.2.trans (hv.2.trans (Nat.sub_le _ _))⟩
    next _ => contradiction

end LowSpaceSubsetSum.BudgetedPrefixController

end OAI
