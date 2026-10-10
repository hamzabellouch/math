import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeys
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedRestriction
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalDependencyRank
import OAI.Combinatorics.EditApproximation.Queries.QueryPhysicalScalarGuards
import OAI.Combinatorics.EditApproximation.Binary.BinaryArithmeticWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Finite-domain guards execute binary comparisons on table coordinates.
Random-source coordinates pass through the guard unchanged. -/

namespace EditApproximation

@[simp] theorem queryNaturalLEWithWork_value (a b : ℕ) :
    (wordLEWithWork a.bits b.bits).1 = true ↔ a ≤ b := by
  simp only [wordLEWithWork_value, bitWordValue_bits]



@[simp] theorem queryPhysicalBoundedWithWork_value {M J n : ℕ}
    (passes copies T S : ℕ) (request : PhysicalTableRequest M J n) :
    (queryPhysicalBoundedWithWork passes copies T S request).1 = true ↔
      request.Bounded passes copies T S := by
  simp only [queryPhysicalBoundedWithWork, Bool.and_eq_true, decide_eq_true_eq,
    binaryNaturalCompareWithWork_lt, wordLEWithWork_value, bitWordValue_bits,
    binaryNaturalAddWithWork_value, PhysicalTableRequest.Bounded]
  tauto

section Body
variable {σ : Type*} {M J n : ℕ} (passes copies T S : ℕ)
  (parent : {r : PhysicalTableRequest M J n // r.Bounded passes copies T S})





@[simp] theorem querySupportedChildWithWork_value
    (key : QueryPhysicalChild (σ := σ) passes copies T S parent) :
    (querySupportedChildWithWork passes copies T S parent key).1 = true ↔
      SourceRanked.supportedChild (PhysicalTableRequest.combinedRank T S)
        (PhysicalTableRequest.Bounded passes copies T S) parent.val key := by
  cases key with
  | inl source => exact iff_of_true rfl trivial
  | inr child => exact queryPhysicalBoundedWithWork_value passes copies T S child.val



theorem queryRestrictPhysicalBody_refines
    (program : BitQuery (QueryPhysicalChild (σ := σ) passes copies T S parent) BinaryFraction)
    (expected : (request : PhysicalTableRequest M J n) →
      FiniteQuery (Sum σ {child : PhysicalTableRequest M J n //
        child.combinedRank T S < request.combinedRank T S}))
    (h : BitQuery.Refines (fun word value => word.value = value) program (expected parent.val)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryRestrictPhysicalBody passes copies T S parent program)
      (SourceRanked.restrictBody (PhysicalTableRequest.combinedRank T S)
        (PhysicalTableRequest.Bounded passes copies T S) expected parent) := by
  classical
  exact (h.restrictWithWork _ _ (querySupportedChildWithWork_value passes copies T S parent)).mapKeysWithWork
    _ _ (fun _ => rfl)

end Body
end EditApproximation

end OAI
