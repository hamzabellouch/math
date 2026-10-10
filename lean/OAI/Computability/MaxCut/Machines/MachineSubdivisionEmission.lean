import Mathlib
import OAI.Computability.MaxCut.Machines.MachineSubdivisionDynamicRows

namespace OAI

/-! Literal output-header emission and the initial occurrence-loop frame. -/

namespace MaxCutGames.Explicit.MachineSubdivisionEmission

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def headerBits (n q Q : Nat) : List Bool := encodeWords [n + 3 * Q, q, 4 * Q]

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineSubdivisionInit.resultTapes n q Q body)
    .accumulator (headerBits n q Q).reverse

theorem header_template (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      headerBits n q Q := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    headerTokens, newHeaderField, MachineSubdivisionInit.resultTapes,
    headerBits, encodeWords]

theorem header_copiedLength (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      n + 7 * Q + 2 := by
  simp [MachineFieldTemplate.copiedLength, headerTokens, newHeaderField,
    MachineSubdivisionInit.resultTapes]
  omega

theorem header_result (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.outputTapes (MachineSubdivisionInit.resultTapes n q Q body)
      .accumulator (headerBits n q Q) = resultTapes n q Q body := by
  simp only [MachineFieldTemplate.outputTapes, MachineSubdivisionInit.resultTapes,
    List.append_nil, resultTapes]

def headerInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, MachineSubdivisionInit.resultTapes n q Q body⟩
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (3 * (n + 7 * Q + 2) + 10) := by
  have run := MachineFieldTemplate.phaseInTime (headerTokens q) newHeaderField
    Tape.copyScratch Tape.accumulator
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide) (by decide)
    (Label.emitHeader : MachineFieldTemplate.Label (headerTokens q).length → Label q)
    (some .guard) (program q) (fun _ => rfl)
    (MachineSubdivisionInit.resultTapes n q Q body) rfl initialState
  rw [header_template, header_copiedLength, header_result] at run
  simpa only [machine, FinTM2.step, FinTM2.Cfg, MachineFieldTemplate.reset, initialState,
    headerTokens, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    using! run

/-- From raw input headers to the running occurrence loop, including all finite
arithmetic phases and literal output-header emission. -/
def prepareInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6 + 9 * MachineSubdivisionInit.stageCost n Q +
        (3 * (n + 7 * Q + 2) + 10)) := by
  have h := MachineSubdivisionHeaders.headersInTime q n Q body
  have i := MachineSubdivisionInit.initializeInTime q n Q body
  have e := headerInTime q n Q body
  have hi := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h i
  have hie := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hi e
  exact {
    toEvalsTo := hie.toEvalsTo
    steps_le_m := by
      have bound := hie.steps_le_m
      omega }

end MaxCutGames.Explicit.MachineSubdivisionEmission

end OAI
