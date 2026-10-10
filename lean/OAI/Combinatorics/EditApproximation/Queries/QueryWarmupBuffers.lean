import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBuffers
import OAI.Combinatorics.EditApproximation.Queries.QueryRepresentatives
import OAI.Combinatorics.EditApproximation.Binary.BinaryWarmupReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



@[simp] theorem queryOverrideParentReadWithWork_value {n : ℕ} (value : BinaryFraction)
    (q : TargetInterval n) (keys : List (TargetInterval n)) (words : List BinaryFraction)
    (r : TargetInterval n) :
    (queryOverrideParentReadWithWork value q keys words r).1.value =
      if r = q then value.value else finiteAnswerTable keys (words.map BinaryFraction.value) r := by
  unfold queryOverrideParentReadWithWork
  by_cases hr : r = q
  · rw [ite_eq_left ((queryIntervalEqualWithWork_value r q).mpr hr), ite_eq_left hr]
  · rw [ite_eq_right (fun h => hr ((queryIntervalEqualWithWork_value r q).mp h)), ite_eq_right hr]
    exact queryParentReadWithWork_value keys words r

theorem queryOverrideParentReadWithWork_cost {n : ℕ} (value : BinaryFraction)
    (q : TargetInterval n) (keys : List (TargetInterval n)) (words : List BinaryFraction)
    (r : TargetInterval n) :
    (queryOverrideParentReadWithWork value q keys words r).2 ≤
      16 * Nat.size n + 7 + keys.length * (16 * Nat.size n + 6) := by
  have ht := queryIntervalEqualWithWork_cost r q (Nat.size n) le_rfl
  have hr := queryParentReadWithWork_cost keys words r
  unfold queryOverrideParentReadWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega



theorem queryWarmupInputsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (I : ℕ) (hi : ∀ r, (initial r).2 ≤ I) :
    (queryWarmupInputsWithWork M parent N P F a initial q).1 =
      wideWarmupInputs parent P
        (localRefinementRepresentatives N P F a.value (fun r => (initial r).1.value) q) := by
  simp only [queryWarmupInputsWithWork, queryWideInputsWithWork_value _ _ _ hP,
    (localRepresentativeReadWithWork_eq_cost N P F a initial q I hi).1,
    localRepresentativesWithWork_value N P F hP]

theorem localWarmupReadKernelWithWork_value_only {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M × TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (I : ℕ) (hi : ∀ r, (initial r).2 ≤ I) :
    (localWarmupReadKernelWithWork parent N P F a initial child q).1.value =
      rationalBellman (fun r => (initial r).1.value) (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent
          (localRefinementRepresentatives N P F a.value (fun r => (initial r).1.value) q) P)
        (fun input => (child input).1.value) q := by
  rw [localWarmupReadKernelWithWork_eq parent N P F a initial child q I hi]
  exact localWarmupKernelWithWork_value parent N P F hP a _ _ q

end EditApproximation.BinaryFraction

end OAI
