import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineSubstitution

namespace OAI


namespace DFVSGames.Reduction.MachineTransducer

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord statementPushBound_pushWord)

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

private theorem update_input_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

private theorem update_output_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

variable {Q : Type} [Fintype Q]

def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

def loop (initial : Q) :
    TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool) :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun state => some (state.1, state.2.getD false))
      (.load (fun _ => (initial, none)) .halt))

def program (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Option (Q × Bool) →
      TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool)
  | none => loop initial
  | some (state, symbol) =>
      .load (fun register => (transition state symbol, register.2))
        (pushWord true (emit state symbol) (.goto fun _ => none))

def machine (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Option (Q × Bool)
  main := none
  σ := Q × Option Bool
  initialState := (initial, none)
  m := program initial transition emit

noncomputable def maxEmission (emit : Q → Bool → List Bool) : Nat :=
  Finset.univ.sup (fun pair : Q × Bool => (emit pair.1 pair.2).length)

theorem emission_le (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool) :
    (emit state symbol).length ≤ maxEmission emit := by
  exact Finset.le_sup (f := fun pair : Q × Bool => (emit pair.1 pair.2).length)
    (Finset.mem_univ (state, symbol))

theorem statementPushBound_le (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (label : Option (Q × Bool)) :
    Runtime.statementPushBound (program initial transition emit label) ≤ maxEmission emit := by
  cases label with
  | none => simp [program, loop, Runtime.statementPushBound]
  | some pair =>
    simpa only [program, Runtime.statementPushBound, statementPushBound_pushWord,
      Nat.add_zero] using emission_le emit pair.1 pair.2

theorem programPushBound_le (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) :
    Runtime.programPushBound (machine initial transition emit) ≤ maxEmission emit := by
  have allLabels (labels : List (Option (Q × Bool))) :
      Runtime.maxLabelPushes (program initial transition emit) labels ≤ maxEmission emit := by
    induction labels with
    | nil => exact Nat.zero_le _
    | cons label rest ih =>
      exact max_le (statementPushBound_le initial transition emit label) ih
  exact allLabels (machine initial transition emit).ΛFin.elems.toList

def running (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (state : Q) (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).Cfg :=
  ⟨some none, (state, register), tapeStacks input accumulator⟩

def emitting (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (oldState : Q) (symbol : Bool) (input accumulator : List Bool)
    (state : Q × Option Bool) : (machine initial transition emit).Cfg :=
  ⟨some (some (oldState, symbol)), state, tapeStacks input accumulator⟩

def halted (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (accumulator : List Bool) : (machine initial transition emit).Cfg :=
  ⟨none, (initial, none), tapeStacks [] accumulator⟩

theorem step_empty (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (accumulator : List Bool)
    (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state [] accumulator register) =
      some (halted initial transition emit accumulator) := by
  change some (TM2.stepAux (loop initial) (state, register) (tapeStacks [] accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted]
  rw [update_input_inline_MachineTransducer]
  rfl

theorem step_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state (symbol :: input) accumulator register) =
      some (emitting initial transition emit state symbol input accumulator (state, some symbol)) := by
  change some (TM2.stepAux (loop initial) (state, register)
    (tapeStacks (symbol :: input) accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input_inline_MachineTransducer]
  rfl

theorem step_emit (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (oldState : Q) (symbol : Bool)
    (input accumulator : List Bool) (state : Q × Option Bool) :
    (machine initial transition emit).step
        (emitting initial transition emit oldState symbol input accumulator state) =
      some (running initial transition emit (transition oldState symbol) input
        ((emit oldState symbol).reverse ++ accumulator) state.2) := by
  change some (TM2.stepAux (pushWord true (emit oldState symbol) (.goto fun _ => none))
    (transition oldState symbol, state.2) (tapeStacks input accumulator)) = _
  rw [stepAux_pushWord]
  simp only [TM2.stepAux]
  change some (⟨some none, (transition oldState symbol, state.2),
    Function.update (tapeStacks input accumulator) true
      ((emit oldState symbol).reverse ++ accumulator)⟩ :
    TM2.Cfg (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool)) = _
  rw [update_output_inline_MachineTransducer]
  rfl

def next (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (configuration : Option (machine initial transition emit).Cfg) :
    Option (machine initial transition emit).Cfg :=
  configuration.bind (machine initial transition emit).step

theorem two_steps_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (next initial transition emit)^[2]
        (some (running initial transition emit state (symbol :: input) accumulator register)) =
      some (running initial transition emit (transition state symbol) input
        ((emit state symbol).reverse ++ accumulator) (some symbol)) := by
  change (machine initial transition emit).step
    (running initial transition emit state (symbol :: input) accumulator register) >>=
      (machine initial transition emit).step = _
  rw [step_cons]
  exact step_emit initial transition emit state symbol input accumulator (state, some symbol)

theorem transduce_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (input accumulator : List Bool)
    (register : Option Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (running initial transition emit state input accumulator register)) =
      some (halted initial transition emit ((output transition emit state input).reverse ++ accumulator)) := by
  induction input generalizing state accumulator register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, output, List.reverse_nil, List.nil_append]
      using step_empty initial transition emit state accumulator register
  | cons symbol input ih =>
    rw [List.length_cons]
    rw [show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega]
    rw [Function.iterate_add_apply, two_steps_cons, ih]
    simp only [output, List.reverse_append, List.append_assoc]

theorem initList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    initList (machine initial transition emit) input =
      running initial transition emit initial input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (accumulator : List Bool) :
    haltList (machine initial transition emit) accumulator =
      halted initial transition emit accumulator := by
  unfold haltList halted
  congr 1

theorem transduce_init_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (next initial transition emit)^[2 * input.length + 1]
        (some (initList (machine initial transition emit) input)) =
      some (haltList (machine initial transition emit) (output transition emit initial input).reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using transduce_steps initial transition emit initial input [] none

def outputsInTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    TM2OutputsInTime (machine initial transition emit) input
      (some (output transition emit initial input).reverse) (2 * input.length + 1) where
  steps := 2 * input.length + 1
  evals_in_steps := transduce_init_steps initial transition emit input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (input : List Bool) :
    (outputsInTime initial transition emit input).steps = 2 * input.length + 1 := rfl

noncomputable def reversedComputableInPolyTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun input => (output transition emit initial input).reverse) where
  tm := machine initial transition emit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 1
  outputsFun input := by
    change TM2OutputsInTime (machine initial transition emit) (input.map id)
      (some ((output transition emit initial input).reverse.map id))
      ((2 * Polynomial.X + 1 : Polynomial Nat).eval input.length)
    have hi := @List.map_id ((machine initial transition emit).Γ
      (machine initial transition emit).k₀) input
    have ho := @List.map_id ((machine initial transition emit).Γ
      (machine initial transition emit).k₁) (output transition emit initial input).reverse
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat, Polynomial.eval_one] using outputsInTime initial transition emit input

noncomputable def computableInPolyTime (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (output transition emit initial) := by
  simpa only [List.reverse_reverse] using
    MachineSequential.composeBits (reversedComputableInPolyTime initial transition emit)
      MachineReverse.computableInPolyTime

end DFVSGames.Reduction.MachineTransducer


namespace DFVSGames.Foundations.Complexity.MachineTransducerCopy

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev Alphabet (K : Type) (_ : K) := Bool
abbrev State (σ Q : Type) := (σ × Q) × Option Bool

def scanLoop (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push scratch (fun state => state.2.getD false)
        (.goto fun state => emitterLabel state.1.2 (state.2.getD false)))
      (.load (fun state => ((state.1.1, initial), none)) (.goto fun _ => restoreLabel)))

def emitter (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    TM2.Stmt (Alphabet K) Λ (State σ Q) :=
  .load (fun state => ((state.1.1, transition control symbol), state.2))
    (pushWord destination (emit control symbol) (.goto fun _ => scanLabel))

abbrev tapes (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input scratchWord outputWord

private theorem update_source_inline_MachineTransducerCopy (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      source replacement = tapes source scratch destination base replacement scratchWord outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, sourceScratch, sourceDestination]
  · by_cases ht : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceScratch, scratchDestination]
    · by_cases hd : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceDestination]
      · simp [tapes, MachineCopy.forkTapes, hs, ht, hd]

private theorem update_scratch_inline_MachineTransducerCopy (source scratch destination : K)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      scratch replacement = tapes source scratch destination base input replacement outputWord := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, scratchDestination]
  · by_cases hd : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm scratchDestination]
    · simp [tapes, MachineCopy.forkTapes, ht, hd]

private theorem update_output_inline_MachineTransducerCopy (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      destination replacement = tapes source scratch destination base input scratchWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanStep_empty (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base [] scratchWord outputWord⟩ =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] scratchWord outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base [] scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source_inline_MachineTransducerCopy]

theorem scanStep_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩ =
      some ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord) outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base (symbol :: input) scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source_inline_MachineTransducerCopy, update_scratch_inline_MachineTransducerCopy]

theorem emitterStep (source scratch destination : K)
    (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (symbol : Bool) :
    TM2.step program ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
      tapes source scratch destination base input scratchWord outputWord⟩ =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input scratchWord
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change some (TM2.stepAux (program (emitterLabel control symbol)) ((ambient, control), some symbol)
    (tapes source scratch destination base input scratchWord outputWord)) = _
  rw [atEmitter]
  simp only [emitter, TM2.stepAux]
  rw [stepAux_pushWord]
  simp only [TM2.stepAux, MachineCopy.forkTapes_right]
  rw [update_output_inline_MachineTransducerCopy]

theorem twoSteps_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩) =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord)
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change (TM2.step program ⟨some scanLabel, ((ambient, control), register),
    tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩).bind
      (TM2.step program) = _
  rw [scanStep_cons source scratch destination sourceScratch sourceDestination scratchDestination
    initial scanLabel restoreLabel emitterLabel program atScan base symbol input scratchWord
    outputWord ambient control register]
  exact emitterStep source scratch destination transition emit scanLabel emitterLabel program
    atEmitter base input (symbol :: scratchWord) outputWord ambient control symbol

theorem scanTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * input.length + 1]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base input scratchWord outputWord⟩) =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] (input.reverse ++ scratchWord)
          ((Reduction.MachineTransducer.output transition emit control input).reverse ++ outputWord)⟩ := by
  induction input generalizing control scratchWord outputWord register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, Reduction.MachineTransducer.output, List.reverse_nil,
      List.nil_append] using
      scanStep_empty source scratch destination sourceScratch sourceDestination scratchDestination
        initial scanLabel restoreLabel emitterLabel program atScan base scratchWord outputWord
        ambient control register
  | cons symbol input ih =>
    rw [List.length_cons, show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega,
      Function.iterate_add_apply]
    rw [twoSteps_cons source scratch destination sourceScratch sourceDestination scratchDestination
      initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
      symbol input scratchWord outputWord ambient control register, ih]
    simp only [Reduction.MachineTransducer.output, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem restoreTapes (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (outputWord : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base [] (base source).reverse outputWord)
      [] (base source) = Function.update base destination outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [Reduction.MachineTransfer.tapesAt, sourceDestination]
  · by_cases ht : k = scratch
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch, scratchDestination, scratchEmpty]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes,
          Ne.symm sourceDestination, Ne.symm scratchDestination]
      · simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem transduceCopyTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * (base source).length + 2]
      (some ⟨some scanLabel, ((ambient, control), register), base⟩) =
      some ⟨exit, ((ambient, initial), none),
        Function.update base destination
          ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
            base destination)⟩ := by
  have scan := scanTrace source scratch destination sourceScratch sourceDestination scratchDestination
    initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
    (base source) (base scratch) (base destination) ambient control register
  have tapesSelf : tapes source scratch destination base (base source) (base scratch)
      (base destination) = base := MachineCopy.forkTapes_self source scratch destination base
  rw [tapesSelf] at scan
  simp only [scratchEmpty, List.append_nil] at scan
  let outputWord :=
    (Reduction.MachineTransducer.output transition emit control (base source)).reverse ++ base destination
  let scanned := tapes source scratch destination base [] (base source).reverse outputWord
  have restore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm sourceScratch)
    id false restoreLabel exit program atRestore scanned (ambient, initial) none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restoreLabel, ((ambient, initial), none), scanned⟩) = _ at restore
  have scratchWord : scanned scratch = (base source).reverse := by
    simp [scanned, scratchDestination]
  have sourceWord : scanned source = [] := by
    simp [scanned, sourceScratch, sourceDestination]
  rw [scratchWord, sourceWord] at restore
  simp only [List.map_id, List.reverse_reverse, List.append_nil, List.length_reverse] at restore
  rw [restoreTapes source scratch destination sourceScratch sourceDestination scratchDestination
    base scratchEmpty outputWord] at restore
  rw [show 3 * (base source).length + 2 =
    ((base source).length + 1) + (2 * (base source).length + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restore

def transduceCopyInTime (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, ((ambient, control), register), base⟩
      (some ⟨exit, ((ambient, initial), none), Function.update base destination
        ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
          base destination)⟩)
      (3 * (base source).length + 2) where
  steps := 3 * (base source).length + 2
  evals_in_steps := transduceCopyTrace source scratch destination sourceScratch sourceDestination
    scratchDestination initial transition emit scanLabel restoreLabel emitterLabel exit program
    atScan atEmitter atRestore base scratchEmpty ambient control register
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in
theorem scanLoop_pushBound (source scratch : K) (initial : Q)
    (emitterLabel : Q → Bool → Λ) (restoreLabel : Λ) :
    Runtime.statementPushBound (scanLoop (σ := σ) source scratch initial emitterLabel restoreLabel) = 1 := by
  simp [scanLoop, Runtime.statementPushBound]

omit [DecidableEq K] in
theorem emitter_pushBound (destination : K) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (scanLabel : Λ) (control : Q) (symbol : Bool) :
    Runtime.statementPushBound (emitter (σ := σ) destination transition emit scanLabel control symbol) =
      (emit control symbol).length := by
  simp [emitter, Runtime.statementPushBound, Reduction.MachineSubstitution.statementPushBound_pushWord]

end DFVSGames.Foundations.Complexity.MachineTransducerCopy


namespace DFVSGames.Reduction.MachineFieldTemplate

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

inductive Token (q : Nat)
  | literal (bits : List Bool)
  | copy (field : Fin q)
  deriving DecidableEq

variable {q : Nat} {K Λ σ : Type}

def tokenOutput (fields : Fin q → List Bool) : Token q → List Bool
  | .literal bits => bits
  | .copy j => fields j

def templateOutput (tokens : List (Token q)) (fields : Fin q → List Bool) : List Bool :=
  tokens.flatMap (tokenOutput fields)

def tokenSteps (fields : Fin q → List Bool) : Token q → Nat
  | .literal _ => 1
  | .copy j => 3 * (fields j).length + 3

def workSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (tokenSteps fields)).sum

def templateSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  workSteps tokens fields + 1

def copiedLength (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (fun t => match t with | .literal _ => 0 | .copy j => (fields j).length)).sum

inductive Label (m : Nat)
  | entry (index : Fin m)
  | scan (index : Fin m)
  | emit (index : Fin m) (symbol : Bool)
  | restore (index : Fin m)
  | done
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet (_ : K) := Bool

def reset (state : State σ) : State σ := ((state.1.1, ()), none)

@[simp] theorem reset_reset (state : State σ) : reset (reset state) = reset state := rfl

def startAt (m i : Nat) : Label m :=
  if h : i < m then .entry ⟨i, h⟩ else .done

def jump (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def identityEmit (_ : Unit) (b : Bool) : List Bool := [b]

def instruction (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (place : Label tokens.length → Λ) (exit : Option Λ) :
    Label tokens.length → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry i => match tokens.get i with
      | .literal bits => .load reset
          (pushWord output bits (.goto fun _ => place (startAt tokens.length (i.val + 1))))
      | .copy _ => .load reset (.goto fun _ => place (.scan i))
  | .scan i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransducerCopy.scanLoop (field j) scratch ()
          (fun _ b => place (.emit i b)) (place (.restore i))
  | .emit i b => MachineTransducerCopy.emitter output (fun _ _ => ()) identityEmit
      (place (.scan i)) () b
  | .restore i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransfer.loopAt scratch (field j) id false
          (place (.restore i)) (some (place (startAt tokens.length (i.val + 1))))
  | .done => .load reset (jump exit)

def program (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (exit : Option (Label tokens.length)) :
    Label tokens.length → TM2.Stmt (Alphabet (K := K)) (Label tokens.length) (State σ) :=
  instruction tokens field scratch output id exit

variable [DecidableEq K]

def outputTapes (base : K → List Bool) (output : K) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem outputTapes_self (base : K → List Bool) (output : K) :
    outputTapes base output [] = base := by simp [outputTapes]

@[simp] theorem outputTapes_output (base : K → List Bool) (output : K) (bits : List Bool) :
    outputTapes base output bits output = bits.reverse ++ base output := by simp [outputTapes]

theorem outputTapes_other (base : K → List Bool) (output : K) (bits : List Bool)
    (tape : K) (different : tape ≠ output) :
    outputTapes base output bits tape = base tape := by simp [outputTapes, different]

theorem outputTapes_append (base : K → List Bool) (output : K) (first second : List Bool) :
    outputTapes (outputTapes base output first) output second =
      outputTapes base output (first ++ second) := by
  simp [outputTapes, List.reverse_append, List.append_assoc]

theorem fieldValues_outputTapes (field : Fin q → K) (output : K)
    (fieldOutput : ∀ j, field j ≠ output) (base : K → List Bool) (bits : List Bool) :
    (fun j => outputTapes base output bits (field j)) = (fun j => base (field j)) := by
  funext j
  exact outputTapes_other base output bits _ (fieldOutput j)

theorem identity_output (bits : List Bool) :
    MachineTransducer.output (fun (_ : Unit) _ => ()) identityEmit () bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [MachineTransducer.output, identityEmit, ih]

private theorem chain_inline_MachineFieldTemplate {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

section Execution

variable (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
variable (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
variable (scratchOutput : scratch ≠ output)
variable (place : Label tokens.length → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction tokens field scratch output place exit label)

include atInstruction

theorem doneStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place .done), state, base⟩ =
      some ⟨exit, reset state, base⟩ := by
  change some (TM2.stepAux (P (place .done)) state base) = _
  rw [atInstruction .done]
  cases exit <;> rfl

theorem literalStep (i : Fin tokens.length) (bits : List Bool)
    (token : tokens.get i = .literal bits) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output bits⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]
  rw [stepAux_pushWord]
  rfl

theorem copySetupStep (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (.scan i)), reset state, base⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]

include fieldScratch fieldOutput scratchOutput

theorem copyTrace (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 3]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (base (field j))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (field j) scratch output (fieldScratch j) (fieldOutput j) scratchOutput
    () (fun _ _ => ()) identityEmit (place (.scan i)) (place (.restore i))
    (fun _ b => place (.emit i b)) (some (place (startAt tokens.length (i.val + 1)))) P
    (by rw [atInstruction (.scan i)]; simp only [instruction, token])
    (by intro control b; cases control; exact atInstruction (.emit i b))
    (by rw [atInstruction (.restore i)]; simp only [instruction, token])
    base scratchEmpty state.1.1 () none
  rw [show 3 * (base (field j)).length + 3 =
      (3 * (base (field j)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 2]
    (TM2.step P ⟨some (place (.entry i)), state, base⟩) = _
  rw [copySetupStep tokens field scratch output place exit P atInstruction i j token]
  simpa only [identity_output, reset, outputTapes] using copied

theorem tokenTrace (i : Fin tokens.length) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[
      tokenSteps (fun j => base (field j)) (tokens.get i)]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (tokenOutput (fun j => base (field j)) (tokens.get i))⟩ := by
  cases token : tokens.get i with
  | literal bits =>
      simpa only [token, tokenSteps, tokenOutput, Function.iterate_one,
        MachineComposition.advance_some] using
        literalStep tokens field scratch output place exit P atInstruction i bits token base state
  | copy j =>
      simpa only [token, tokenSteps, tokenOutput] using
        copyTrace tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
          atInstruction i j token base scratchEmpty state

private theorem suffixTrace_inline_MachineFieldTemplate (remaining : Nat) :
    ∀ (i : Nat), i + remaining = tokens.length →
      ∀ (base : K → List Bool) (_scratchEmpty : base scratch = []) (state : State σ),
        (MachineComposition.advance (TM2.step P))^[
          workSteps (tokens.drop i) (fun j => base (field j)) + 1]
          (some ⟨some (place (startAt tokens.length i)), state, base⟩) =
          some ⟨exit, reset state, outputTapes base output
            (templateOutput (tokens.drop i) (fun j => base (field j)))⟩ := by
  induction remaining with
  | zero =>
      intro i hi base _scratchEmpty state
      have heq : i = tokens.length := by omega
      subst i
      simpa [startAt, workSteps, templateOutput, MachineComposition.advance_some] using
        doneStep tokens field scratch output place exit P atInstruction base state
  | succ remaining ih =>
      intro i hi base scratchEmpty state
      have hiLt : i < tokens.length := by omega
      let index : Fin tokens.length := ⟨i, hiLt⟩
      let bits := tokenOutput (fun j => base (field j)) (tokens.get index)
      let after := outputTapes base output bits
      have first := tokenTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
        place exit P atInstruction index base scratchEmpty state
      have second := ih (i + 1) (by omega) after
        (by simpa [after, outputTapes, scratchOutput] using scratchEmpty) (reset state)
      have fieldsAfter : (fun j => after (field j)) = (fun j => base (field j)) :=
        fieldValues_outputTapes field output fieldOutput base bits
      rw [fieldsAfter] at second
      have combined := chain_inline_MachineFieldTemplate first second
      simp only [reset_reset, after, outputTapes_append] at combined
      have dropHead : tokens.drop i = tokens.get index :: tokens.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt tokens.length i = .entry index := by
        simp [startAt, hiLt, index]
      rw [hstart, dropHead]
      simp only [templateOutput, List.flatMap_cons]
      change _ = some (⟨exit, reset state, outputTapes base output
        (bits ++ templateOutput (tokens.drop (i + 1)) (fun j => base (field j)))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ))
      convert combined using 1
      congr 1
      simp only [workSteps, List.map_cons, List.sum_cons]
      omega

theorem phaseTrace (base : K → List Bool) (scratchEmpty : base scratch = [])
    (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[templateSteps tokens (fun j => base (field j))]
      (some ⟨some (place (startAt tokens.length 0)), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩ := by
  simpa only [Nat.zero_add, List.drop_zero, templateSteps] using
    suffixTrace_inline_MachineFieldTemplate tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
      atInstruction tokens.length 0 (by omega) base scratchEmpty state

end Execution

theorem programTrace (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (exit : Option (Label tokens.length))
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step (program tokens field scratch output exit)))^[
      templateSteps tokens (fun j => base (field j))]
      (some ⟨some (startAt tokens.length 0), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩ :=
  phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput id exit
    (program tokens field scratch output exit) (fun _ => rfl) base scratchEmpty state

theorem templateSteps_le (tokens : List (Token q)) (fields : Fin q → List Bool) :
    templateSteps tokens fields ≤ 3 * copiedLength tokens fields + 3 * tokens.length + 1 := by
  have workBound : workSteps tokens fields ≤
      3 * copiedLength tokens fields + 3 * tokens.length := by
    induction tokens with
    | nil => simp [workSteps, copiedLength]
    | cons token tokens ih =>
        cases token <;>
          simp only [workSteps, copiedLength, List.map_cons, List.sum_cons,
            tokenSteps, List.length_cons] at * <;> omega
  unfold templateSteps
  omega

def phaseInTime (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label tokens.length → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction tokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt tokens.length 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩)
      (3 * copiedLength tokens (fun j => base (field j)) + 3 * tokens.length + 1) where
  steps := templateSteps tokens (fun j => base (field j))
  evals_in_steps := phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  steps_le_m := templateSteps_le tokens _

end DFVSGames.Reduction.MachineFieldTemplate

end OAI
