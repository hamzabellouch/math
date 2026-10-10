import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupBuffers
import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A warmup step uses two adaptive gathers.  The first determines its
representatives; the second requests exactly their distinct child states. -/

namespace EditApproximation

section Warmup
variable {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
  (N P F : ℕ) (hP : 0 < P) (a : BinaryFraction)
  (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
  (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
  (q : TargetInterval ny)



include hP in
theorem queryWarmupProgram_refines
    (expectedInitial : TargetInterval ny → FiniteQuery ι)
    (expectedChild : (Fin M × TargetInterval ny) → FiniteQuery ι)
    (hi : ∀ r, BitQuery.Refines (fun word value => word.value = value) (initialRead r) (expectedInitial r))
    (hc : ∀ input, BitQuery.Refines (fun word value => word.value = value)
      (childRead input) (expectedChild input)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryWarmupProgram parent N P F a initialRead childRead q)
      (localWarmupStepQuery parent N P F a.value expectedInitial expectedChild q) := by
  unfold queryWarmupProgram localWarmupStepQuery
  apply (hi q).bind
  intro value answer hv
  subst answer
  apply BitQuery.Refines.charge
  change BitQuery.Refines _ (BitQuery.collect initialRead _ _) _
  rw [BinaryFraction.queryRawCentersWithWork_value N P F hP]
  apply BitQuery.Refines.collect initialRead expectedInitial hi
  intro words
  let centers := rawRefinementCenters N P F a.value value.value q
  let initial := BinaryFraction.queryOverrideParentReadWithWork value q centers words
  let I := 16 * Nat.size ny + 7 + centers.length * (16 * Nat.size ny + 6)
  have hI (r : TargetInterval ny) : (initial r).2 ≤ I :=
    BinaryFraction.queryOverrideParentReadWithWork_cost value q centers words r
  apply BitQuery.Refines.charge
  change BitQuery.Refines _ (BitQuery.collect childRead _ _) _
  rw [BinaryFraction.queryWarmupInputsWithWork_value M parent N P F hP a initial q I hI]
  simp only [initial, BinaryFraction.queryOverrideParentReadWithWork_value]
  apply BitQuery.Refines.collect childRead expectedChild hc
  intro childWords
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.done
  rw [BinaryFraction.localWarmupReadKernelWithWork_value_only parent N P F hP a initial _ q I hI]
  simp only [initial, BinaryFraction.queryOverrideParentReadWithWork_value,
    BinaryFraction.queryChildReadWithWork_value]
  rfl

end Warmup
end EditApproximation

end OAI
