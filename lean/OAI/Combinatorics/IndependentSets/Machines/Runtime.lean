import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LoopInitialization
import OAI.Combinatorics.IndependentSets.PCP.Finish

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

noncomputable def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C 27 * Polynomial.X + Polynomial.C 54 +
    Polynomial.X *
      (Polynomial.C (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) *
        (Polynomial.X + Polynomial.C 1)) + Polynomial.C 1

theorem prefixPolynomial_eval (q N : Nat) :
    (prefixPolynomial q).eval N = Loop.prefixTime q N := by
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Loop.prefixTime,
    Initialization.time, Body.bodyTime]
  ring

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

noncomputable def tableOutputsInTime {q : Nat} (input : GenericGraphTables.Table q) :
    TM2OutputsInTime (Driver.machine q) (GenericGraphTables.tableBits input)
      (some (GraphTables.tableBits (Table.build input)))
      ((time q).eval (GenericGraphTables.tableBits input).length) := by
  let prefixRun := Loop.runPrefix input
  have hrun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal prefixRun.relation prefixRun.flag, prefixRun.tapes⟩)
      ((prefixPolynomial q).eval (GenericGraphTables.tableBits input).length) := by
    rw [prefixPolynomial_eval]
    exact prefixRun.run
  exact Finish.finishAfterPolynomialPrefix q (GenericGraphTables.tableBits input)
    prefixRun.tapes (GraphTables.tableBits (Table.build input))
    (normal prefixRun.relation prefixRun.flag) (prefixPolynomial q) hrun
    prefixRun.ready.reversed_at_end prefixRun.ready.output

noncomputable def tablePolynomialTime (q : Nat) :
    TM2ComputableInPolyTime (GenericGraphTables.tableBits (q := q))
      GraphTables.tableBits (Table.build (q := q)) where
  tm := Driver.machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time q
  outputsFun input := by
    change TM2OutputsInTime (Driver.machine q)
      ((GenericGraphTables.tableBits input).map id)
      (some ((GraphTables.tableBits (Table.build input)).map id))
      ((time q).eval (GenericGraphTables.tableBits input).length)
    convert! tableOutputsInTime input using 1
    · exact congrArg (TM2OutputsInTime (Driver.machine q)) (List.map_id _)
    · exact congrArg some (List.map_id _)

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Runtime

end OAI
