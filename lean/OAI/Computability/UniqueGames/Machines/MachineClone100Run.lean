import OAI.Computability.UniqueGames.Machines.MachineClone100Headers
import OAI.Computability.UniqueGames.Machines.MachineClone100Loop
import OAI.Computability.UniqueGames.Machines.MachineClone100TableLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Run

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

def tm (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 :=
  machine triples nonempty

def emptyTapes : Tape → List Bool := fun _ => []

def sourceBody (input : SourceEncoding.Input) : List Bool :=
  encodeWords (input.equations.flatMap SourceEncoding.equationWords)

def outputHeaders (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords [100 * input.variables, triples.length * input.equations.length]

def outputBody (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  encodeWords (input.equations.flatMap fun equation =>
    triples.flatMap (MachineClone100Table.cloneEquationWords equation))

def outputBits (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    List Bool :=
  outputHeaders triples input ++ outputBody triples input

def inputTapes (input : SourceEncoding.Input) : Tape → List Bool :=
  fun tape => if tape = .input then SourceEncoding.inputBits input else []

def guardTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes (sourceBody input) (encodeWord input.equations.length)
    (outputHeaders triples input).reverse (fun _ => [])

def afterLoopTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes [] (encodeWord 0)
    ((outputBody triples input).reverse ++ (outputHeaders triples input).reverse) (fun _ => [])

theorem inputBits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.variables, input.equations.length] ++ sourceBody input := by
  simp only [SourceEncoding.inputBits, SourceEncoding.inputWords, encodeWords_append, sourceBody]

theorem initList_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    initList (tm triples nonempty) (SourceEncoding.inputBits input) =
      ⟨some (.headerStart 0), initialState triples.length, inputTapes input⟩ := by
  change (⟨some (.headerStart 0), initialState triples.length,
    (initList (tm triples nonempty) (SourceEncoding.inputBits input)).stk⟩ :
    (tm triples nonempty).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (.headerStart 0), initialState triples.length, tapes⟩ : (tm triples nonempty).Cfg))
  funext tape
  cases tape <;> simp [initList, tm, machine, inputTapes]
  rfl

theorem headers_result_eq (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    MachineClone100Headers.resultTapes triples (inputTapes input)
      input.variables input.equations.length (sourceBody input) = guardTapes triples input := by
  funext tape
  cases tape <;> simp [MachineClone100Headers.resultTapes, inputTapes, guardTapes,
    MachineClone100Loop.tapes, emptyTapes, outputHeaders]

theorem afterLoop_reversed (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).reverse = outputBits triples input := by
  simp only [afterLoopTapes, MachineClone100Loop.tapes, List.reverse_append,
    List.reverse_reverse, outputBits]

theorem afterLoop_length (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).length = (outputBits triples input).length := by
  calc
    _ = ((afterLoopTapes triples input .reversed).reverse).length := List.length_reverse.symm
    _ = _ := congrArg List.length (afterLoop_reversed triples input)

theorem finish_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    (⟨none, initialState triples.length,
      MachineClone100Finish.finishTapes (afterLoopTapes triples input)⟩ :
      (tm triples nonempty).Cfg) =
        haltList (tm triples nonempty) (outputBits triples input) := by
  have finished := MachineClone100Finish.finish_eq_haltList triples nonempty
    (afterLoopTapes triples input) (by
      intro tape counter reversed
      cases tape <;> simp_all [afterLoopTapes, MachineClone100Loop.tapes, emptyTapes])
  simpa only [afterLoop_reversed, tm] using finished

/-- Actual execution from the existing input codec to the complete literal
halt configuration, with the sum of the three proved phase budgets. -/
def runInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    TM2OutputsInTime (tm triples nonempty) (SourceEncoding.inputBits input)
      (some (outputBits triples input))
      (((outputBits triples input).length + 2) +
        (((2 + 3 * triples.length) * (sourceBody input).length +
            (9 + 12 * triples.length) * input.equations.length + 1) +
          (5 * input.variables + 4 * input.equations.length + 18))) := by
  let first := MachineClone100Headers.headersInTime triples nonempty
    (inputTapes input) input.variables input.equations.length (sourceBody input)
    (by simpa only [inputTapes, ite_true] using inputBits_eq input) rfl rfl rfl rfl
  have first' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      (initList (tm triples nonempty) (SourceEncoding.inputBits input))
      (some ⟨some .guard, initialState _, guardTapes triples input⟩)
      (5 * input.variables + 4 * input.equations.length + 18) := by
    rw [initList_eq, ← headers_result_eq]
    exact first
  let middle := MachineClone100Loop.sourceLoopInTime_table triples nonempty
    (n := input.variables) input.equations emptyTapes [] (outputHeaders triples input).reverse
  have middle' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, guardTapes triples input⟩
      (some ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩)
      ((2 + 3 * triples.length) * (sourceBody input).length +
        (9 + 12 * triples.length) * input.equations.length + 1) := by
    simpa only [List.append_nil, guardTapes, afterLoopTapes, sourceBody, outputBody] using middle
  let last := MachineClone100Finish.finishInTime triples nonempty (afterLoopTapes triples input) rfl
  have last' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩
      (some (haltList (tm triples nonempty) (outputBits triples input)))
      ((outputBits triples input).length + 2) := by
    rw [← afterLoop_length, ← finish_eq]
    exact last
  let firstTwo := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ first' middle'
  let allThree := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ firstTwo last'
  exact { toEvalsTo := allThree.toEvalsTo, steps_le_m := allThree.steps_le_m }

end UniqueGamesTheorem.Explicit.MachineClone100Run

end

end OAI
