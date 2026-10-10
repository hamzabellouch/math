import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Binary.BinaryDistanceWork
import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryRestriction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Key tagging and finite-domain restriction preserve the adaptive
reference program. Executed key tests carry their actual Boolean cost. -/

namespace EditApproximation.BitQuery



theorem Refines.mapKeysWithWork {ι κ β : Type*} {relation : β → ℚ → Prop}
    (f : ι → κ × ℕ) (g : ι → κ) (hf : ∀ key, (f key).1 = g key)
    {program : BitQuery ι β} {expected : FiniteQuery ι}
    (h : Refines relation program expected) :
    Refines relation (mapKeysWithWork f program) (FiniteQuery.mapKeys g expected) := by
  induction h with
  | done h => exact .done h
  | charge steps h ih => exact .charge steps ih
  | read key next expected h ih =>
    apply Refines.charge
    change Refines relation (.read (f key).1 _) (.read (g key) _)
    rw [hf key]
    exact .read _ _ _ ih


theorem mapKeysWithWork_work {ι κ β : Type*} (f : ι → κ × ℕ)
    (program : BitQuery ι β) (oracle : κ → BinaryFraction) (readWork : κ → ℕ) :
    (mapKeysWithWork f program).work oracle readWork =
      program.work (fun key => oracle (f key).1) (fun key => (f key).2 + readWork (f key).1) := by
  induction program with
  | done result => rfl
  | charge steps next ih => exact congrArg (steps + ·) ih
  | read key next ih =>
    simp only [mapKeysWithWork, work, ih, Nat.add_assoc]



theorem Refines.restrictWithWork {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : Refines (fun word value => word.value = value) program expected) :
    Refines (fun word value => word.value = value)
      (restrictWithWork P test htest program) (FiniteQuery.restrict P expected) := by
  induction h with
  | done h => exact .done h
  | charge steps h ih => exact .charge steps ih
  | read key next expected h ih =>
    apply Refines.charge
    change Refines _ (dite ((test key).1 = true) _ _) (dite (P key) _ _)
    by_cases hp : P key
    · have ht := (htest key).mpr hp
      rw [dite_eq_left ht, dite_eq_left hp]
      exact .read _ _ _ ih
    · have ht : (test key).1 ≠ true := fun ht => hp ((htest key).mp ht)
      rw [dite_eq_right ht, dite_eq_right hp]
      simpa only [BinaryFraction.nat_value, Nat.cast_zero] using ih (BinaryFraction.nat 0)

end EditApproximation.BitQuery

end OAI
