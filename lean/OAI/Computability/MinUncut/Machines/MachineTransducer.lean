import Mathlib
import OAI.Computability.MinUncut.Search.ArithmeticExpression
import OAI.Computability.MinUncut.Machines.MachineSubstitution

namespace OAI

section
namespace MinUncutGames.Reduction.MachineTransducer

open Turing
open MinUncutGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord statementPushBound_pushWord)

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

theorem update_input (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output (input output replacement : List Bool) :
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
  exact congrArg (fun st => (some ⟨none, (initial, none), st⟩ :
    Option (TM2.Cfg (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool))))
    (update_input [] accumulator [])

theorem step_cons (initial : Q) (transition : Q → Bool → Q)
    (emit : Q → Bool → List Bool) (state : Q) (symbol : Bool)
    (input accumulator : List Bool) (register : Option Bool) :
    (machine initial transition emit).step
        (running initial transition emit state (symbol :: input) accumulator register) =
      some (emitting initial transition emit state symbol input accumulator (state, some symbol)) := by
  change some (TM2.stepAux (loop initial) (state, register)
    (tapeStacks (symbol :: input) accumulator)) = _
  simp [loop, TM2.stepAux, tapeStacks, emitting]
  rw [update_input]
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
    (machine initial transition emit).Cfg) = _
  exact congrArg (fun st =>
    (some ⟨some none, (transition oldState symbol, state.2), st⟩ :
      Option (TM2.Cfg (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool))))
    (update_output input accumulator ((emit oldState symbol).reverse ++ accumulator))

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

end MinUncutGames.Reduction.MachineTransducer

end
section
namespace MinUncutGames.Foundations.Complexity.MachineTransducerCopy

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

theorem update_source (source scratch destination : K)
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

theorem update_scratch (source scratch destination : K)
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

theorem update_output (source scratch destination : K) (base : K → List Bool)
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
    update_source]

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
    update_source, update_scratch]

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
  rw [update_output]

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

end MinUncutGames.Foundations.Complexity.MachineTransducerCopy

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyDrain, .copyFork, .seed, .guard, .scan,
  .emitFalse, .emitTrue, .restore, .finish]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .copyDrain => Reduction.MachineTransfer.loopAt (slots 1) (slots 4) id false
      (labels .copyDrain) (some (labels .copyFork))
  | .copyFork => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .copyFork) (some (labels .seed))
  | .seed => .push (slots 2) (fun _ => false) (.goto fun _ => labels .guard)
  | .guard => MachineUnaryCounter.guard (slots 3) (labels .scan) (labels .finish)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore)
  | .emitFalse => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () false
  | .emitTrue => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () true
  | .restore => Reduction.MachineTransfer.loopAt (slots 4) (slots 0) id false
      (labels .restore) (some (labels .guard))
  | .finish => .pop (slots 3) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 2) exit)

def program (slots : Fin 5 ↪ K) : Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement slots id none

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .copyDrain
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Fin 5))

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ)
    (k : K) (hk : k ≠ slots 2) : resultTapes slots base p k = base k := by
  simp [resultTapes, hk]

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

theorem output_encodeWord (a : ℕ) :
    Reduction.MachineTransducer.output transition payload () (encodeWord a) =
      List.replicate a true := by
  induction a with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ a ih =>
    simpa only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, Bool.cond_true, transition,
      ite_true, List.singleton_append, List.nil_append] using congrArg (List.cons true) ih

private theorem prepend_payload (a p : ℕ) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord p ++ suffix) = encodeWord (a + p) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

def loopBase (slots : Fin 5 ↪ K) (base : K → List Bool) (a b r : ℕ) : K → List Bool :=
  resultTapes slots base (a * (b - r))

theorem bodyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b r : ℕ) (hr : r < b)
    (operand : base (slots 0) = encodeWord a) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[bodySteps a]
      (some (MachineCountedLoop.bodyConfiguration (slots 3) (labels .scan) []
        (fun _ => (ambient, ())) (loopBase slots base a b) r)) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) r) := by
  have h04 : slots 0 ≠ slots 4 := slots.injective.ne (by decide)
  have h02 : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have h42 : slots 4 ≠ slots 2 := slots.injective.ne (by decide)
  have h03 : slots 0 ≠ slots 3 := slots.injective.ne (by decide)
  have h43 : slots 4 ≠ slots 3 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let start := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b (r + 1)) r []
  have hstartA : start (slots 0) = encodeWord a := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h03, h02, operand]
  have hstartScratch : start (slots 4) = [] := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h43, h42, scratchEmpty]
  have hscan : p (labels .scan) = MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore) := atLabels .scan
  have hemit : ∀ control bit, p (emitterLabel labels control bit) =
      MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) control bit := by
    intro control bit
    cases control
    cases bit <;> exact atLabels _
  have hrestore : p (labels .restore) = Reduction.MachineTransfer.loopAt (slots 4) (slots 0)
      id false (labels .restore) (some (labels .guard)) := atLabels .restore
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 4) (slots 2)
    h04 h02 h42 () transition payload (labels .scan) (labels .restore) (emitterLabel labels)
    (some (labels .guard)) p hscan hemit hrestore start hstartScratch ambient () none
  rw [hstartA, output_encodeWord, List.reverse_replicate] at hcopy
  have hcount : a + a * (b - (r + 1)) = a * (b - r) := by
    have hr' : b - r = b - (r + 1) + 1 := by omega
    rw [hr']
    ring
  have hfinish : Function.update start (slots 2)
      (List.replicate a true ++ start (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b r) r [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp only [Function.update_self]
      simp only [start, MachineUnaryCounter.counterTapes_other (slots 3) (slots 2) h23,
        loopBase, resultTapes_output]
      rw [prepend_payload, hcount]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [start, MachineUnaryCounter.counterTapes, hk2]
      · simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  rw [hfinish] at hcopy
  simpa only [bodySteps, encodeWord, List.length_append, List.length_replicate,
    List.length_singleton, MachineCountedLoop.bodyConfiguration,
    MachineCountedLoop.guardConfiguration] using hcopy

private theorem totalSteps_eq (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

theorem multiplyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps a b]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
  have h13 : slots 1 ≠ slots 3 := slots.injective.ne (by decide)
  have h14 : slots 1 ≠ slots 4 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let copied := Function.update base (slots 3) (encodeWord b)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (b + 2)]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .seed), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4) h13 h14 h34 false
      (labels .copyDrain) (labels .copyFork) (some (labels .seed)) p
      (atLabels .copyDrain) (atLabels .copyFork) base scratchEmpty (ambient, ()) register
    simpa only [copied, operandB, counterEmpty, List.append_nil, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using h
  have hseedTapes : Function.update copied (slots 2) (false :: copied (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b b) b [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h23, encodeWord]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [copied, MachineUnaryCounter.counterTapes, hk2]
      · simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), none), copied⟩) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) b) := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), none) copied) = _
    rw [atLabels .seed]
    change some (⟨some (labels .guard), ((ambient, ()), none),
      Function.update copied (slots 2) (false :: copied (slots 2))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [hseedTapes]
    rfl
  have hloop := MachineCountedLoop.loopTrace (slots 3) (labels .guard) (labels .scan)
    (labels .finish) p (atLabels .guard) [] (fun _ => (ambient, ())) (fun _ => none)
    (loopBase slots base a b) (fun _ => bodySteps a) b
    (fun r hr => bodyTrace slots labels exit p atLabels base a b r hr operandA scratchEmpty ambient)
  let finalCounter := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b 0) 0 []
  have hfinishTapes : Function.update finalCounter (slots 3) ((finalCounter (slots 3)).tail) =
      resultTapes slots base (a * b) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp [finalCounter, MachineUnaryCounter.counterTapes, encodeWord, resultTapes,
        Ne.symm h23, counterEmpty]
    · simp [finalCounter, MachineUnaryCounter.counterTapes, loopBase, hk3]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some (MachineCountedLoop.exitConfiguration (slots 3) (labels .finish) []
        (fun _ => (ambient, ())) (loopBase slots base a b))) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) finalCounter) = _
    rw [atLabels .finish]
    cases exit <;>
      simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using
        congrArg (fun tapes => some (⟨_, ((ambient, ()), none), tapes⟩ :
          TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
  rw [show steps a b = 1 + (MachineCountedLoop.totalSteps (fun _ => bodySteps a) b +
      (1 + 2 * (b + 2))) by rw [totalSteps_eq]; unfold steps bodySteps; ring]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hcopy, hseed, hloop]
  exact hfinish

def multiplyInTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩) (steps a b) where
  steps := steps a b
  evals_in_steps := multiplyTrace slots labels exit p atLabels base a b operandA operandB
    counterEmpty scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X + Polynomial.C 7

theorem steps_le_timePolynomial (a b : ℕ) :
    steps a b ≤ timePolynomial.eval (a + b + 2) := by
  have ha : a ≤ a + b + 2 := by omega
  have hb : b ≤ a + b + 2 := by omega
  have hab := Nat.mul_le_mul ha hb
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

theorem multiplyFrame (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (k : K) (hk : k ≠ slots 2) :
    resultTapes slots base (a * b) k = base k := resultTapes_other slots base _ k hk

theorem programTrace (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program (σ := σ) slots)))^[steps a b]
      (some ⟨some .copyDrain, ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes slots base (a * b)⟩ :=
  multiplyTrace slots id none (program slots) (fun _ => rfl) base a b
    operandA operandB counterEmpty scratchEmpty ambient register

def programInPolynomialTime (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots))
      ⟨some .copyDrain, ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes slots base (a * b)⟩)
      (timePolynomial.eval ((encodeWord a).length + (encodeWord b).length)) where
  steps := steps a b
  evals_in_steps := programTrace slots base a b operandA operandB counterEmpty scratchEmpty ambient register
  steps_le_m := by
    have hlength : (encodeWord a).length + (encodeWord b).length = a + b + 2 := by
      simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [hlength]
    exact steps_le_timePolynomial a b

end MinUncutGames.Foundations.Complexity.MachineUnaryMultiply

end

end OAI
