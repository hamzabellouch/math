import OAI.Combinatorics.EditApproximation.Queries.QueryInitialConeCenters
import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The initial-cone program first reads its seed, constructs the actual
raw-center list, gathers its answers, and executes the cached Boolean
initial kernel with that finite buffer. -/

namespace EditApproximation

section Initial
variable {ι α : Type*} (source target : List α)
  (N P F : ℕ) (hP : 0 < P) (A a : BinaryFraction)
  (reader : TargetInterval target.length → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)



def queryInitialConeProgram : BitQuery ι BinaryFraction :=
  queryInitialConeProgramAt source.length N P F A a reader q

include hP in
theorem queryInitialConeProgram_refines
    (expected : TargetInterval target.length → FiniteQuery ι)
    (hr : ∀ r, BitQuery.Refines (fun word value => word.value = value) (reader r) (expected r))
    (ha : a.value = refinementFactor A.value F) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryInitialConeProgram source target N P F A a reader q)
      (FiniteQuery.bind (expected q) fun answer =>
        let value := ⌈answer⌉₊
        let keys := rawInitialConeCenters N P A.value value q
        FiniteQuery.collect expected keys fun answers =>
          let localTable := fun r => if r = q then value else ⌈finiteAnswerTable keys answers r⌉₊
          .done (localInitialConeTable source target localTable N P F A.value (refinementFactor A.value F) q)) := by
  unfold queryInitialConeProgram queryInitialConeProgramAt
  apply (hr q).bind
  intro value answer hv
  subst answer
  apply BitQuery.Refines.charge
  change BitQuery.Refines _ (BitQuery.collect reader _ _) _
  rw [BinaryFraction.queryInitialConeCentersWithWork_value N P hP]
  apply BitQuery.Refines.collect reader expected hr
  intro words
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.done
  rw [BinaryFraction.cachedInitialProgramReadWithWork_value_only source target N P F hP]
  simp only [BinaryFraction.queryInitialSeedReadWithWork_value, ha]

theorem queryInitialConeProgram_work (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let value := (reader q).value oracle
    let keys := BinaryFraction.queryInitialConeCentersWithWork N P A value q
    let words := keys.1.map fun r => (reader r).value oracle
    (queryInitialConeProgram source target N P F A a reader q).work oracle readWork =
      (reader q).work oracle readWork + keys.2 +
        (keys.1.map fun r => (reader r).work oracle readWork + 3).sum +
        (BinaryFraction.cachedInitialProgramReadWithWork source.length N P F A a
          (BinaryFraction.queryInitialSeedReadWithWork value q keys.1 words) q).2 := by
  simp only [queryInitialConeProgram, queryInitialConeProgramAt, BitQuery.work_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero, Nat.add_assoc]

end Initial
end EditApproximation

end OAI
