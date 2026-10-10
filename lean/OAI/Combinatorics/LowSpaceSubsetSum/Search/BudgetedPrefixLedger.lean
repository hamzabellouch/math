import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedPrefixAllowance

namespace OAI

namespace LowSpaceSubsetSum.BudgetedPrefixController

variable {n : ℕ}

/-- The shared-budget allowance is charged to the original full prefix tree,
including the exact list of completed checks. -/
theorem allowance_le_ledger (D : RepresentationParentData n) (B : ℕ)
    (collect : StoredRestriction n → StoredEntry.Dictionary D.input D.capacity)
    (hcollect : ∀ P, StoredDictionaryJoin.erase D.input D.capacity (collect P) =
      ({D with maskRestriction := P.semantic}.collect B).state.user)
    (collectBill : StoredRestriction n → ℕ) (checkBill : Array (StoredEntry n) → ℕ)
    (semanticCheckBill : Array (Entry (Fin n)) → ℕ)
    (hcheck : ∀ a, checkBill a = semanticCheckBill (a.map StoredEntry.semantic))
    (A M R K : ℕ)
    (hbill : ∀ P, collectBill P ≤ A * (D.capacity + 1) +
      M * ({D with maskRestriction := P.semantic}.localLedger B).queries +
      R * ({D with maskRestriction := P.semantic}.localLedger B).reports +
      K * ({D with maskRestriction := P.semantic}.localLedger B).copies)
    (order : List (Fin n)) (P : StoredRestriction n) :
    allowance collect collectBill checkBill order P ≤
      (A * (D.capacity + 1) + StoredPrefixController.header n) * D.taskStarts B order P.semantic +
      M * (D.prefixLedger B order P.semantic).queries +
      R * (D.prefixLedger B order P.semantic).reports +
      K * (D.prefixLedger B order P.semantic).copies +
      ((D.completedArrays B order P.semantic).map semanticCheckBill).sum := by
  have hk P := congrArg RecordedDictionary.State.keys (hcollect P)
  have hr P := congrArg RecordedDictionary.State.records (hcollect P)
  change ∀ P, (collect P).val.keys = _ at hk
  change ∀ P, (collect P).val.records.map StoredEntry.semantic = _ at hr
  induction order generalizing P with
  | nil =>
    have hb := hbill P
    simp only [allowance, hk, hcheck, hr, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split <;> simp only [List.map_nil, List.map_cons, List.sum_nil, List.sum_cons,
      Nat.mul_one, Nat.add_zero]
    · omega
    · omega
  | cons i order ih =>
    have hb := hbill P
    have h₀ := ih (P.force i false).1
    have h₁ := ih (P.force i true).1
    simp only [StoredRestriction.force_value] at h₀ h₁
    simp only [allowance, hk, hcheck, hr, RepresentationParentData.taskStarts,
      RepresentationParentData.prefixLedger, RepresentationParentData.completedArrays]
    split
    · simp only [CompressionLedger.add, List.map_append, List.sum_append, Nat.mul_add, Nat.mul_one]
      simp only [Nat.mul_add, Nat.mul_one] at hb h₀ h₁
      omega
    · simp only [List.map_nil, List.map_cons, List.sum_nil, List.sum_cons, Nat.mul_one, Nat.add_zero]
      omega

end LowSpaceSubsetSum.BudgetedPrefixController

end OAI
