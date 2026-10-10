import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.CookLevin.CircuitEncodingBridge

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem drainStep_cons (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (bit : Bool) (input : List Bool)
    (control : Unit × Context) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape (bit :: input)⟩ =
      some ⟨some again, (control, some bit), Function.update base tape input⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape (bit :: input))) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainStep_nil (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape []⟩ =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape [])) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainTrace (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (input : List Bool)
    (control : Unit × Context) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (control, register), Function.update base tape input⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  induction input generalizing register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        MachineComposition.advance_some] using
        drainStep_nil tape again next atAgain base control register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[input.length + 1]
        (TM2.step program ⟨some again, (control, register),
          Function.update base tape (bit :: input)⟩) = _
      rw [drainStep_cons tape again next atAgain, ih]

theorem drainTrace_base (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(base tape).length + 1]
      (some ⟨some again, (control, register), base⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self] using
    drainTrace tape again next atAgain base (base tape) control register

def drainInTime (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (control, register), base⟩
      (some ⟨some next, (control, none), Function.update base tape []⟩)
      ((base tape).length + 1) where
  steps := (base tape).length + 1
  evals_in_steps := drainTrace_base tape again next atAgain base control register
  steps_le_m := Nat.le_refl _

theorem tagStep (tag : Fin 5) (base : Tape → List Bool) (state : State)
    (htag : base (.field 0) = encodeWord tag.val) :
    TM2.step program ⟨some .decodeTag, state, base⟩ =
      some ⟨some (.setup (.gate tag 0)), initialState,
        Function.update base (.field 0) []⟩ := by
  fin_cases tag <;>
    simp [TM2.step, TM2.stepAux, program, tagDecoder, resetGoto, initialState,
      encodeWord, htag]

def tagInTime (tag : Fin 5) (base : Tape → List Bool) (state : State)
    (htag : base (.field 0) = encodeWord tag.val) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .decodeTag, state, base⟩
      (some ⟨some (.setup (.gate tag 0)), initialState,
        Function.update base (.field 0) []⟩) 1 where
  steps := 1
  evals_in_steps := tagStep tag base state htag
  steps_le_m := Nat.le_refl _

def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]

theorem clearFields_other (base : Tape → List Bool) (tape : Tape)
    (h : ∀ j, tape ≠ .field j) : clearFields base tape = base tape := by
  simp [clearFields, h]

def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

theorem cleanupTrace (base : Tape → List Bool) (control : Unit × Context)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let b1 := Function.update base (.field 0) []
  let b2 := Function.update b1 (.field 1) []
  let b3 := Function.update b2 (.field 2) []
  have h0 := drainTrace_base (.field 0) (.cleanup 0) (.cleanup 1) rfl
    base control register
  have h1 := drainTrace_base (.field 1) (.cleanup 1) (.cleanup 2) rfl b1 control none
  have h2 := drainTrace_base (.field 2) (.cleanup 2) (.cleanup 3) rfl b2 control none
  have h3 := drainTrace_base (.field 3) (.cleanup 3) .guard rfl b3 control none
  have hn : cleanupSteps base = ((b3 (.field 3)).length + 1) +
      ((b2 (.field 2)).length + 1) + ((b1 (.field 1)).length + 1) +
      ((base (.field 0)).length + 1) := by
    simp [cleanupSteps, b1, b2, b3]
    omega
  rw [hn, Function.iterate_add_apply, h0, Function.iterate_add_apply, h1,
    Function.iterate_add_apply, h2, h3]
  rfl

def cleanupInTime (base : Tape → List Bool) (control : Unit × Context)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := cleanupTrace base control register
  steps_le_m := Nat.le_refl _

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output
    (Function.update (Function.update base .counter []) .selected []) []
    ((base .reversed).reverse ++ base .output)

theorem counterStep (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step program ⟨some .finalCounter, initialState, base⟩ =
      some ⟨some .clearSelected, initialState, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

theorem finishTrace (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step program))^[
      (base .selected).length + (base .reversed).length + 3]
      (some ⟨some .finalCounter, initialState, base⟩) =
      some ⟨none, initialState, finishTapes base⟩ := by
  let b1 := Function.update base .counter []
  let b2 := Function.update b1 .selected []
  have first := counterStep base hcounter
  have second := drainTrace_base .selected .clearSelected .finalReverse rfl
    b1 ((), defaultControl) none
  have last := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false Label.finalReverse none program rfl b2
    ((), defaultControl) none
  have hnext : MachineTransfer.nextAt Tape.output program =
      MachineComposition.advance (TM2.step program) := rfl
  rw [hnext] at last
  have last' : (MachineComposition.advance (TM2.step program))^[(base .reversed).length + 1]
      (some ⟨some .finalReverse, initialState, b2⟩) =
      some ⟨none, initialState, finishTapes base⟩ := by
    simpa [finishTapes, b1, b2,
      initialState] using last
  have second' : (MachineComposition.advance (TM2.step program))^[(base .selected).length + 1]
      (some ⟨some .clearSelected, initialState, b1⟩) =
      some ⟨some .finalReverse, initialState, b2⟩ := by
    simpa [b1, initialState] using second
  rw [show (base .selected).length + (base .reversed).length + 3 =
      ((base .reversed).length + 1) + ((base .selected).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first,
    Function.iterate_add_apply, second', last']

def finishInTime (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .finalCounter, initialState, base⟩
      (some ⟨none, initialState, finishTapes base⟩)
      ((base .selected).length + (base .reversed).length + 3) where
  steps := (base .selected).length + (base .reversed).length + 3
  evals_in_steps := finishTrace base hcounter
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

def parsedTapes (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | .selected => encodeWord output
  | tape => base tape

def resultTapes (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => []
  | .counter => encodeWord m
  | .selected => encodeWord output
  | .reversed => (encodeWords [n, 3 * m + 1]).reverse
  | tape => base tape

theorem parsedTapes_eq (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool)
    (hn : base .header = []) (hm : base .counter = []) (ho : base .selected = []) :
    SourceMachine.afterField .input .selected
      (SourceMachine.afterField .input .counter
        (SourceMachine.afterField .input .header base n
          (encodeWords [m, output] ++ suffix)) m (encodeWord output ++ suffix))
      output suffix = parsedTapes base n m output suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hn, hm, ho]

theorem headersTrace (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m, output] ++ suffix)
    (hn : base .header = []) (hm : base .counter = []) (ho : base .selected = [])
    (hs : base .scratch = []) (hr : base .reversed = []) :
    (MachineComposition.advance (TM2.step program))^[5 * n + 4 * m + output + 20]
      (some ⟨some (.headerStart 0), initialState, base⟩) =
      some ⟨some .guard, initialState, resultTapes base n m output suffix⟩ := by
  let b0 := SourceMachine.afterField .input .header base n
    (encodeWords [m, output] ++ suffix)
  let b1 := SourceMachine.afterField .input .counter b0 m (encodeWord output ++ suffix)
  let b2 := parsedTapes base n m output suffix
  let b3 := Function.update b2 .reversed (encodeWord n).reverse
  let b4 := Function.update b2 .reversed (encodeWords [n, 3 * m + 1]).reverse
  have h0 : base .input = encodeWord n ++ (encodeWords [m, output] ++ suffix) := by
    simpa only [encodeWords, List.append_nil, List.append_assoc] using hinput
  have h1 : b0 .input = encodeWord m ++ (encodeWord output ++ suffix) := by
    simp [b0, SourceMachine.afterField, encodeWords, List.append_assoc]
  have h2 : b1 .input = encodeWord output ++ suffix := by
    simp [b1, SourceMachine.afterField]
  have p0 := (SourceMachine.fieldInTime .input .header (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    base n (encodeWords [m, output] ++ suffix) h0 ((), defaultControl) none).evals_in_steps
  have p1 := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some (.headerStart 2)) program rfl rfl
    b0 m (encodeWord output ++ suffix) h1 ((), defaultControl) none).evals_in_steps
  have p2 := (SourceMachine.fieldInTime .input .selected (by decide)
    (.headerStart 2) (.headerLoop 2) (some (.setup (.header 0))) program rfl rfl
    b1 output suffix h2 ((), defaultControl) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, base⟩) =
    some ⟨some (.headerStart 1), initialState, b0⟩ at p0
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, b0⟩) =
    some ⟨some (.headerStart 2), initialState, b1⟩ at p1
  change (MachineComposition.advance (TM2.step program))^[output + 2]
    (some ⟨some (.headerStart 2), initialState, b1⟩) =
    some ⟨some (.setup (.header 0)), initialState,
      SourceMachine.afterField .input .selected b1 output suffix⟩ at p2
  have hb2 : SourceMachine.afterField .input .selected b1 output suffix = b2 :=
    parsedTapes_eq base n m output suffix hn hm ho
  rw [hb2] at p2
  have p3 : (MachineComposition.advance (TM2.step program))^[3 * (n + 1) + 3]
      (some ⟨some (.setup (.header 0)), initialState, b2⟩) =
      some ⟨some (.setup (.header 1)), initialState, b3⟩ := by
    simpa [contextWords, contextNext, b3, b2, parsedTapes, hr, encodeWords] using
      contextTrace_word (.header 0) b2 (by simpa [b2, parsedTapes] using hs)
        initialState n rfl
  have p4 : (MachineComposition.advance (TM2.step program))^[3 * (m + 1) + 3]
      (some ⟨some (.setup (.header 1)), initialState, b3⟩) =
      some ⟨some .clearHeader, initialState, b4⟩ := by
    have p := contextTrace_word (.header 1) b3
      (by simpa [b3, b2, parsedTapes] using hs) initialState m (by
        simp [b3, b2, parsedTapes, contextSource])
    simpa [contextWords, contextNext, b4, b3, encodeWords, List.reverse_append] using p
  have p5 : (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some .clearHeader, initialState, b4⟩) =
      some ⟨some .guard, initialState, resultTapes base n m output suffix⟩ := by
    have p := drainTrace_base .header .clearHeader .guard rfl b4
      ((), defaultControl) none
    have he : Function.update b4 .header [] = resultTapes base n m output suffix := by
      funext tape
      cases tape <;> simp [b4, b2, parsedTapes, resultTapes]
    rw [he] at p
    simpa [b4, b2, parsedTapes, initialState] using p
  rw [show 5 * n + 4 * m + output + 20 = (n + 2) +
      (3 * (m + 1) + 3) + (3 * (n + 1) + 3) + (output + 2) +
      (m + 2) + (n + 2) by omega,
    Function.iterate_add_apply, p0, Function.iterate_add_apply, p1,
    Function.iterate_add_apply, p2, Function.iterate_add_apply, p3,
    Function.iterate_add_apply, p4, p5]

def headersInTime (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m, output] ++ suffix)
    (hn : base .header = []) (hm : base .counter = []) (ho : base .selected = [])
    (hs : base .scratch = []) (hr : base .reversed = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.headerStart 0), initialState, base⟩
      (some ⟨some .guard, initialState, resultTapes base n m output suffix⟩)
      (5 * n + 4 * m + output + 20) where
  steps := 5 * n + 4 * m + output + 20
  evals_in_steps := headersTrace base n m output suffix hinput hn hm ho hs hr
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

def recordsInput (rs : List Record) : List Bool := rs.flatMap Record.bits
def recordsOutput (rs : List Record) : List Bool := rs.flatMap Record.outputBits

def tapes (base : Tape → List Bool) (input counter accumulator : List Bool)
    (fields : Fin 4 → List Bool) : Tape → List Bool
  | .input => input
  | .counter => counter
  | .field j => fields j
  | .scratch => []
  | .reversed => accumulator
  | tape => base tape

def parsedFields (r : Record) (j : Fin 4) : List Bool := encodeWord (r.fieldValue j)
def decodedFields (r : Record) (j : Fin 4) : List Bool :=
  if j.val = 0 then [] else parsedFields r j

theorem update_reversed (base : Tape → List Bool) (input counter acc out : List Bool)
    (fields : Fin 4 → List Bool) :
    Function.update (tapes base input counter acc fields) .reversed out =
      tapes base input counter out fields := by
  funext tape
  cases tape <;> simp [tapes]

theorem counterTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes .counter
      (tapes base input counter acc fields) n [] =
      tapes base input (encodeWord n) acc fields := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem fourTapes_eq (base : Tape → List Bool) (input counter acc suffix : List Bool)
    (r : Record) :
    SourceMachine.fourTapes .input Tape.field
      (tapes base input counter acc (fun _ => [])) r.tag.val r.output r.first r.second suffix =
      tapes base suffix counter acc (parsedFields r) := by
  funext tape
  cases tape with
  | field j =>
      fin_cases j <;>
        simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
          tapes, parsedFields, Record.fieldValue]
  | _ =>
      simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
        tapes]

theorem decodeTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    Function.update (tapes base input counter acc (parsedFields r)) (.field 0) [] =
      tapes base input counter acc (decodedFields r) := by
  funext tape
  cases tape with
  | field j => fin_cases j <;> simp [tapes, decodedFields]
  | _ => simp [tapes]

theorem clearFields_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) :
    clearFields (tapes base input counter acc fields) =
      tapes base input counter acc (fun _ => []) := by
  funext tape
  cases tape with
  | field j => simp [tapes]
  | _ => simp [tapes, clearFields]

theorem cleanupSteps_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    cleanupSteps (tapes base input counter acc (decodedFields r)) =
      r.output + r.first + r.second + 7 := by
  simp [cleanupSteps, tapes, decodedFields, parsedFields, Record.fieldValue]
  omega

theorem recordBits_length (r : Record) :
    r.bits.length = r.tag.val + r.output + r.first + r.second + 4 := by
  simp [Record.bits, Record.words, encodeWords]
  omega

def bodyCost (r : Record) : Nat :=
  (r.tag.val + r.output + r.first + r.second + 8) + 1 +
    gateSteps r + (r.output + r.first + r.second + 7)

def bodyInTime (base : Tape → List Bool) (r : Record) (suffix counter acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.fieldStart 0), initialState,
        tapes base (r.bits ++ suffix) counter acc (fun _ => [])⟩
      (some ⟨some .guard, initialState,
        tapes base suffix counter (r.outputBits.reverse ++ acc) (fun _ => [])⟩)
      (bodyCost r) := by
  let before := tapes base (r.bits ++ suffix) counter acc (fun _ => [])
  let parsed := tapes base suffix counter acc (parsedFields r)
  let decoded := tapes base suffix counter acc (decodedFields r)
  let out := r.outputBits.reverse ++ acc
  let emitted := tapes base suffix counter out (decodedFields r)
  let parse := SourceMachine.fourFieldsInTime .input Tape.field
    (by intro j h; cases h) Label.fieldStart Label.fieldLoop (some .decodeTag)
    program (by intro j; rfl) (by intro j; rfl)
    before r.tag.val r.output r.first r.second suffix rfl ((), defaultControl) none
  have hp : SourceMachine.fourTapes .input Tape.field before
      r.tag.val r.output r.first r.second suffix = parsed := fourTapes_eq _ _ _ _ _ _
  rw [hp] at parse
  let decode := tagInTime r.tag parsed initialState rfl
  have hd : Function.update parsed (.field 0) [] = decoded := decodeTapes_eq _ _ _ _ _
  rw [hd] at decode
  let table := gateInTime r decoded rfl initialState rfl rfl rfl
  have he : Function.update decoded .reversed (r.outputBits.reverse ++ decoded .reversed) =
      emitted := update_reversed _ _ _ _ _ _
  rw [he] at table
  let cleanup := cleanupInTime emitted ((), defaultControl) none
  have hc : clearFields emitted = tapes base suffix counter out (fun _ => []) :=
    clearFields_eq _ _ _ _ _
  rw [hc] at cleanup
  let p1 := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parse decode
  let p2 := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p1 table
  let p3 := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p2 cleanup
  exact {
    toEvalsTo := p3.toEvalsTo
    steps_le_m := by
      have h := p3.steps_le_m
      have hcost : cleanupSteps emitted = r.output + r.first + r.second + 7 :=
        cleanupSteps_eq _ _ _ _ _
      unfold bodyCost
      omega }

def loopCost : List Record → Nat
  | [] => 1
  | r :: rs => (1 + bodyCost r) + loopCost rs

def loopInTime (base : Tape → List Bool) (suffix : List Bool)
    (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, initialState,
        tapes base (recordsInput rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some (.setup (.output 0)), initialState,
        tapes base suffix (encodeWord 0) ((recordsOutput rs).reverse ++ acc) (fun _ => [])⟩)
      (loopCost rs) := by
  induction rs generalizing acc with
  | nil =>
      let guard := MachineUnaryCounter.guardInTime_zero .counter Label.guard
        (.fieldStart 0) (.setup (.output 0)) program rfl
        (tapes base suffix (encodeWord 0) acc (fun _ => [])) []
        ((), defaultControl) none
      simpa only [counterTapes_eq, loopCost, recordsInput, recordsOutput,
        List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
        initialState] using guard
  | cons r rs ih =>
      let before := tapes base (r.bits ++ (recordsInput rs ++ suffix))
        (encodeWord (rs.length + 1)) acc (fun _ => [])
      let guard := MachineUnaryCounter.guardInTime_succ .counter Label.guard
        (.fieldStart 0) (.setup (.output 0)) program rfl before rs.length []
        ((), defaultControl) none
      simp only [before, counterTapes_eq] at guard
      let body := bodyInTime base r (recordsInput rs ++ suffix) (encodeWord rs.length) acc
      let rest := ih (r.outputBits.reverse ++ acc)
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
      let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa only [loopCost, recordsInput, recordsOutput, List.flatMap_cons,
        List.length_cons, List.reverse_append, List.append_assoc, initialState,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem bodyCost_le (r : Record) : bodyCost r ≤ 50 * r.bits.length := by
  have h := gateSteps_le r
  rw [recordBits_length]
  unfold bodyCost
  omega

theorem loopCost_le (rs : List Record) :
    loopCost rs ≤ 50 * (recordsInput rs).length + rs.length + 1 := by
  induction rs with
  | nil => simp [loopCost, recordsInput]
  | cons r rs ih =>
      have h := bodyCost_le r
      simp only [loopCost, recordsInput, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      omega

theorem recordOutput_length_le (r : Record) : r.outputBits.length ≤ 9 * r.bits.length := by
  have h := outputBits_length_le r
  rw [recordBits_length]
  omega

theorem recordsOutput_length_le (rs : List Record) :
    (recordsOutput rs).length ≤ 9 * (recordsInput rs).length := by
  induction rs with
  | nil => simp [recordsOutput, recordsInput]
  | cons r rs ih =>
      have h := recordOutput_length_le r
      simp only [recordsOutput, recordsInput, List.flatMap_cons, List.length_append] at *
      omega

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime

open Turing
open CircuitProducerModel CircuitProducerLoop

structure Input where
  wireCount : Nat
  selected : Nat
  records : List Record

def inputBits (input : Input) : List Bool :=
  encodeWords [input.wireCount, input.records.length, input.selected] ++ recordsInput input.records

def outputHeaders (input : Input) : List Bool :=
  encodeWords [input.wireCount, 3 * input.records.length + 1]

def producedBits (input : Input) : List Bool :=
  outputHeaders input ++ recordsOutput input.records ++ encodeWords (outputWords input.selected)

def inputTapes (input : Input) : Tape → List Bool :=
  fun tape => if tape = .input then inputBits input else []

def retainedTapes (input : Input) : Tape → List Bool :=
  fun tape => if tape = .selected then encodeWord input.selected else []

def guardTapes (input : Input) : Tape → List Bool :=
  tapes (retainedTapes input) (recordsInput input.records) (encodeWord input.records.length)
    (outputHeaders input).reverse (fun _ => [])

def afterLoopTapes (input : Input) : Tape → List Bool :=
  tapes (retainedTapes input) [] (encodeWord 0)
    ((recordsOutput input.records).reverse ++ (outputHeaders input).reverse) (fun _ => [])

def beforeFinishTapes (input : Input) : Tape → List Bool :=
  tapes (retainedTapes input) [] (encodeWord 0) (producedBits input).reverse (fun _ => [])

theorem initList_eq (input : Input) :
    initList machine (inputBits input) =
      ⟨some (.headerStart 0), initialState, inputTapes input⟩ := by
  change (⟨some (.headerStart 0), initialState,
    (initList machine (inputBits input)).stk⟩ : machine.Cfg) = _
  apply congrArg (fun tapeContents =>
    (⟨some (.headerStart 0), initialState, tapeContents⟩ : machine.Cfg))
  funext tape
  (cases tape <;> simp [initList, machine, inputTapes]); rfl

theorem headers_result_eq (input : Input) :
    CircuitProducerHeaders.resultTapes (inputTapes input) input.wireCount
      input.records.length input.selected (recordsInput input.records) = guardTapes input := by
  funext tape
  cases tape <;> simp [CircuitProducerHeaders.resultTapes, inputTapes, guardTapes,
    tapes, retainedTapes, outputHeaders]

theorem output_result_eq (input : Input) :
    Function.update (afterLoopTapes input) .reversed
      ((encodeWords (outputWords input.selected)).reverse ++ afterLoopTapes input .reversed) =
      beforeFinishTapes input := by
  rw [afterLoopTapes, update_reversed]
  simp [beforeFinishTapes, producedBits, tapes, List.reverse_append, List.append_assoc]

theorem finish_eq (input : Input) :
    (⟨none, initialState,
      CircuitProducerStages.finishTapes (beforeFinishTapes input)⟩ : machine.Cfg) =
      haltList machine (producedBits input) := by
  apply congrArg (fun tapeContents => (⟨none, initialState, tapeContents⟩ : machine.Cfg))
  funext tape
  (cases tape <;>
    simp [CircuitProducerStages.finishTapes, Reduction.MachineTransfer.tapesAt,
      beforeFinishTapes, tapes, retainedTapes, machine]); rfl

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.wireCount + input.records.length + input.selected + 3 +
      (recordsInput input.records).length := by
  simp [inputBits, encodeWords]
  omega

theorem producedBits_length_le (input : Input) :
    (producedBits input).length ≤ input.wireCount + 3 * input.records.length +
      3 * input.selected + 9 * (recordsInput input.records).length + 12 := by
  have h := recordsOutput_length_le input.records
  simp only [producedBits, outputHeaders, List.length_append, outputWords, encodeWords,
    encodeWord_length, List.length_nil]
  omega

def fullRunInTime (input : Input) :
    TM2OutputsInTime machine (inputBits input) (some (producedBits input))
      (100 * (inputBits input).length + 100) := by
  let first := CircuitProducerHeaders.headersInTime (inputTapes input) input.wireCount
    input.records.length input.selected (recordsInput input.records) rfl rfl rfl rfl rfl rfl
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine (inputBits input))
      (some ⟨some .guard, initialState, guardTapes input⟩)
      (5 * input.wireCount + 4 * input.records.length + input.selected + 20) := by
    simpa only [initList_eq, headers_result_eq] using! first
  let middle := loopInTime (retainedTapes input) [] input.records (outputHeaders input).reverse
  have middle' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, initialState, guardTapes input⟩
      (some ⟨some (.setup (.output 0)), initialState, afterLoopTapes input⟩)
      (loopCost input.records) := by
    simpa only [List.append_nil, guardTapes, afterLoopTapes] using middle
  let unitClause := CircuitEmission.outputInTime input.selected (afterLoopTapes input)
    rfl initialState rfl
  have unitClause' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.output 0)), initialState, afterLoopTapes input⟩
      (some ⟨some .finalCounter, initialState, beforeFinishTapes input⟩)
      (9 * (input.selected + 1) + 9) := by
    simpa only [output_result_eq] using unitClause
  let last := CircuitProducerStages.finishInTime (beforeFinishTapes input) rfl
  have last' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .finalCounter, initialState, beforeFinishTapes input⟩
      (some (haltList machine (producedBits input)))
      (input.selected + (producedBits input).length + 4) := by
    erw [finish_eq] at last
    convert last using 1
    simp [beforeFinishTapes, tapes, retainedTapes]
    omega
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first' middle'
  let firstThree := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo unitClause'
  let complete := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstThree last'
  refine { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans ?_ }
  have hlo := loopCost_le input.records
  have hout := producedBits_length_le input
  rw [inputBits_length]
  omega

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits (id : List Bool → List Bool) producedBits where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * Polynomial.X + Polynomial.C 100
  outputsFun input := by
    change TM2OutputsInTime machine ((inputBits input).map id)
      (some ((producedBits input).map id)) _
    have input_eq : @List.map (machine.Γ machine.k₀) (machine.Γ machine.k₀) id
        (inputBits input) = inputBits input := List.map_id _
    have output_eq : @List.map (machine.Γ machine.k₁) (machine.Γ machine.k₁) id
        (producedBits input) = producedBits input := List.map_id _
    simpa only [Equiv.refl, input_eq, output_eq, id_eq,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using fullRunInTime input

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

open Turing
open CircuitProducerModel

def asInput (C : Circuit) : CircuitProducerRuntime.Input :=
  ⟨C.wires, C.output.val, C.records⟩

theorem recordsInput_eq (rs : List Record) :
    CircuitProducerLoop.recordsInput rs = encodeWords (rs.flatMap Record.words) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [CircuitProducerLoop.recordsInput, List.flatMap_cons, encodeWords_append] at *
      rw [ih]
      rfl

theorem recordsOutput_eq (rs : List Record) :
    CircuitProducerLoop.recordsOutput rs = encodeWords (rs.flatMap Record.outputWords) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [CircuitProducerLoop.recordsOutput, List.flatMap_cons, encodeWords_append] at *
      rw [ih]
      rfl

theorem inputBits_asInput (C : Circuit) :
    CircuitProducerRuntime.inputBits (asInput C) = circuitBits C := by
  simp only [CircuitProducerRuntime.inputBits, asInput, Circuit.records_length,
    recordsInput_eq, circuitBits, circuitWords, encodeWords_append, recordsWords]

theorem producedBits_asInput (C : Circuit) :
    CircuitProducerRuntime.producedBits (asInput C) = formulaBits C.toFormula := by
  rw [formulaBits, C.formulaWords_eq_records]
  simp only [CircuitProducerRuntime.producedBits, CircuitProducerRuntime.outputHeaders,
    asInput, Circuit.records_length, recordsOutput_eq, encodeWords_append]

def fullRunInTime (C : Circuit) :
    TM2OutputsInTime machine (circuitBits C) (some (formulaBits C.toFormula))
      (100 * (circuitBits C).length + 100) := by
  simpa only [inputBits_asInput, producedBits_asInput] using
    CircuitProducerRuntime.fullRunInTime (asInput C)

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime circuitBits formulaBits Circuit.toFormula where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * Polynomial.X + Polynomial.C 100
  outputsFun C := by
    change TM2OutputsInTime machine ((circuitBits C).map id)
      (some ((formulaBits C.toFormula).map id)) _
    have input_eq : @List.map (machine.Γ machine.k₀) (machine.Γ machine.k₀) id
        (circuitBits C) = circuitBits C := List.map_id _
    have output_eq : @List.map (machine.Γ machine.k₁) (machine.Γ machine.k₁) id
        (formulaBits C.toFormula) = formulaBits C.toFormula := List.map_id _
    simpa only [Equiv.refl, input_eq, output_eq,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using fullRunInTime C

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

end OAI
