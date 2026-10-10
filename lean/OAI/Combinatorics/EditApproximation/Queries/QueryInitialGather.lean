import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupport
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The first adaptive gather executes its binary support construction
after reading the parent value, then requests those keys in their original
order. Its continuation receives only the stored words actually read. -/

namespace EditApproximation



theorem queryInitialGather_refines {ι β : Type*} {n : ℕ} {relation : β → ℚ → Prop}
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction)
    (expectedReader : TargetInterval n → FiniteQuery ι)
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (expectedNext : List (TargetInterval n) → List ℚ → FiniteQuery ι)
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (reader key) (expectedReader key))
    (hn : ∀ (value : BinaryFraction) (words : List BinaryFraction), BitQuery.Refines relation
      (next (refinementInitialSupport N P F exponent a.value value.value q) words)
      (expectedNext (refinementInitialSupport N P F exponent a.value value.value q)
        (words.map BinaryFraction.value))) :
    BitQuery.Refines relation (queryInitialGather N P F exponent hP a q reader next)
      (FiniteQuery.bind (expectedReader q) fun value =>
        let keys := refinementInitialSupport N P F exponent a.value value q
        FiniteQuery.collect expectedReader keys (expectedNext keys)) := by
  apply (hr q).bind
  intro value expected hv
  subst expected
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect reader _ _) _
  rw [BinaryFraction.queryInitialSupportWithWork_value]
  exact BitQuery.Refines.collect reader expectedReader hr _ _ _ (hn value)

theorem queryInitialGather_work {ι β : Type*} {n : ℕ}
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction) (q : TargetInterval n)
    (reader : TargetInterval n → BitQuery ι BinaryFraction)
    (next : List (TargetInterval n) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let value := (reader q).value oracle
    let support := BinaryFraction.queryInitialSupportWithWork N P F exponent hP a value q
    (queryInitialGather N P F exponent hP a q reader next).work oracle readWork =
      (reader q).work oracle readWork + support.2 +
      (support.1.map fun key => (reader key).work oracle readWork + 3).sum +
      (next support.1 (support.1.map fun key => (reader key).value oracle)).work oracle readWork := by
  simp only [queryInitialGather, BitQuery.work_bind, BitQuery.compute,
    BitQuery.work, BitQuery.value, BitQuery.work_collect, Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
