import OAI.Combinatorics.EditApproximation.Queries.QueryInitialGather
import OAI.Combinatorics.EditApproximation.Queries.QueryRepresentatives
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The band-data stage constructs its keys by counted Boolean routines,
then gathers mass and initial words in the reference order. -/

namespace EditApproximation



theorem queryBandGather_refines {ι β : Type*} {nx ny : ℕ} {relation : β → ℚ → Prop}
    (M : ℕ) (parent : TargetInterval nx) (N P F exponent : ℕ) (hP : 0 < P)
    (a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R)
    (massReader initialReader : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (expectedMass expectedInitial : (Fin M × TargetInterval ny) → FiniteQuery ι)
    (next : List (Fin M × TargetInterval ny) → List BinaryFraction → List BinaryFraction →
      BitQuery ι β)
    (expectedNext : List (Fin M × TargetInterval ny) → List ℚ → List ℚ → FiniteQuery ι)
    (hm : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (massReader key) (expectedMass key))
    (hi : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (initialReader key) (expectedInitial key))
    (hn : ∀ mass words,
      let keys := refinementBandInputList (M := M) parent N P F exponent a.value
        (fun r => (initial r).1.value) q
      BitQuery.Refines relation (next keys mass words)
        (expectedNext keys (mass.map BinaryFraction.value) (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryBandGather M parent N P F exponent hP a initial q massReader initialReader next)
      (let keys := refinementBandInputList (M := M) parent N P F exponent a.value
        (fun r => (initial r).1.value) q
       FiniteQuery.collect expectedMass keys fun mass =>
         FiniteQuery.collect expectedInitial keys (expectedNext keys mass)) := by
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect massReader _ _) _
  rw [BinaryFraction.queryBandInputsWithWork_value M parent N P F exponent hP a initial q R hR]
  apply BitQuery.Refines.collect massReader expectedMass hm
  intro mass
  exact BitQuery.Refines.collect initialReader expectedInitial hi _ _ _ (hn mass)

theorem queryBandGather_work {ι β : Type*} {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (massReader initialReader : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (next : List (Fin M × TargetInterval ny) → List BinaryFraction → List BinaryFraction →
      BitQuery ι β) (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let keys := BinaryFraction.queryBandInputsWithWork M parent N P F exponent hP a initial q
    (queryBandGather M parent N P F exponent hP a initial q massReader initialReader next).work
        oracle readWork = keys.2 +
      (keys.1.map fun key => (massReader key).work oracle readWork + 3).sum +
      (keys.1.map fun key => (initialReader key).work oracle readWork + 3).sum +
      (next keys.1 (keys.1.map fun key => (massReader key).value oracle)
        (keys.1.map fun key => (initialReader key).value oracle)).work oracle readWork := by
  simp only [queryBandGather, BitQuery.work_bind, BitQuery.compute,
    BitQuery.work, BitQuery.value, BitQuery.work_collect, Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
