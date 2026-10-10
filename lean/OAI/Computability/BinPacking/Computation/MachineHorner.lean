import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Computation.MachineCloudPrefix
import OAI.Computability.BinPacking.Reductions.MachineTransducer

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineTransducerCopy

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

private theorem update_source (source scratch destination : K)
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

private theorem update_scratch (source scratch destination : K)
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

private theorem update_output (source scratch destination : K) (base : K → List Bool)
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

end BinPackingGames.Foundations.Complexity.MachineTransducerCopy

namespace BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

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

private theorem output_encodeWord (a : ℕ) :
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

private theorem bodyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
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

end BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

namespace BinPackingGames.Foundations.Complexity.MachineRadixStep

open Turing

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

variable {K Λ σ : Type}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineUnaryMultiply.State σ

def multiplySlots (slots : Fin 6 ↪ K) : Fin 5 ↪ K :=
  (Fin.succAboveEmb (2 : Fin 6)).trans slots

@[simp] theorem multiplySlots_zero (slots : Fin 6 ↪ K) : multiplySlots slots 0 = slots 0 := rfl
@[simp] theorem multiplySlots_one (slots : Fin 6 ↪ K) : multiplySlots slots 1 = slots 1 := rfl
@[simp] theorem multiplySlots_two (slots : Fin 6 ↪ K) : multiplySlots slots 2 = slots 3 := rfl
@[simp] theorem multiplySlots_three (slots : Fin 6 ↪ K) : multiplySlots slots 3 = slots 4 := rfl
@[simp] theorem multiplySlots_four (slots : Fin 6 ↪ K) : multiplySlots slots 4 = slots 5 := rfl

variable [DecidableEq K]

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .multiply label => MachineUnaryMultiply.statement (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) label
  | .digitDrain => Reduction.MachineTransfer.loopAt (slots 2) (slots 5) id false
      (labels .digitDrain) (some (labels .digitFork))
  | .digitFork => MachineCopy.forkLoop (slots 5) (slots 2) (slots 4) false
      (labels .digitFork) (some (labels .add))
  | .add => MachineUnaryAddAt.loop (slots 4) (slots 3) (labels .add) (some (labels .finish))
  | .finish => .pop (slots 4) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 3) exit)

def program (slots : Fin 6 ↪ K) : Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement slots id none

def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .multiply .copyDrain
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Fin 6))

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ)
    (k : K) (hk : k ≠ slots 3) : resultTapes slots base value k = base k := by
  simp [resultTapes, hk]

def steps (radix acc digit : ℕ) : ℕ := 3 * radix * acc + 8 * acc + 3 * digit + 13

theorem radixStepTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix acc digit]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  have h24 : slots 2 ≠ slots 4 := slots.injective.ne (by decide)
  have h25 : slots 2 ≠ slots 5 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h53 : slots 5 ≠ slots 3 := slots.injective.ne (by decide)
  have h45 : slots 4 ≠ slots 5 := slots.injective.ne (by decide)
  let multiplied := resultTapes slots base (radix * acc)
  have hmul : (MachineComposition.advance (TM2.step p))^[MachineUnaryMultiply.steps radix acc]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩ := by
    have h := MachineUnaryMultiply.multiplyTrace (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) p
      (fun l => atLabels (.multiply l)) base radix acc operandRadix operandAcc
      counterEmpty scratchEmpty ambient register
    simpa only [MachineUnaryMultiply.resultTapes, multiplySlots_two, multiplied, resultTapes] using h
  have hmulDigit : multiplied (slots 2) = encodeWord digit := by
    simp [multiplied, resultTapes, h23, operandDigit]
  have hmulCounter : multiplied (slots 4) = [] := by
    simp [multiplied, resultTapes, Ne.symm h34, counterEmpty]
  have hmulScratch : multiplied (slots 5) = [] := by
    simp [multiplied, resultTapes, h53, scratchEmpty]
  let copied := Function.update multiplied (slots 4) (encodeWord digit)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (digit + 2)]
      (some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩) =
      some ⟨some (labels .add), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 2) (slots 4) (slots 5) h24 h25 h45 false
      (labels .digitDrain) (labels .digitFork) (some (labels .add)) p
      (atLabels .digitDrain) (atLabels .digitFork) multiplied hmulScratch (ambient, ()) none
    simpa only [copied, hmulDigit, hmulCounter, List.append_nil, encodeWord,
      List.length_append, List.length_replicate, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd] using h
  have hcopiedCounter : copied (slots 4) = encodeWord digit ++ [] := by simp [copied]
  have hcopiedOutput : copied (slots 3) = encodeWord (radix * acc) ++ base (slots 3) := by
    simp [copied, multiplied, resultTapes, h34]
  let added := MachineUnaryAddAt.unaryTapes (slots 4) (slots 3) copied
    0 (digit + radix * acc) [] (base (slots 3))
  have hadd : (MachineComposition.advance (TM2.step p))^[digit + 1]
      (some ⟨some (labels .add), ((ambient, ()), none), copied⟩) =
      some ⟨some (labels .finish), ((ambient, ()), none), added⟩ :=
    MachineUnaryAddAt.addFromTapes (slots 4) (slots 3) (Ne.symm h34)
      (labels .add) (some (labels .finish)) p (atLabels .add) copied digit (radix * acc)
      [] (base (slots 3)) hcopiedCounter hcopiedOutput (ambient, ()) none
  have hfinishTapes : Function.update added (slots 4) ((added (slots 4)).tail) =
      resultTapes slots base (radix * acc + digit) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp only [Function.update_of_ne h34, added, MachineUnaryAddAt.unaryTapes_destination,
        resultTapes_output]
      rw [Nat.add_comm digit (radix * acc)]
    · by_cases hk4 : k = slots 4
      · subst k
        simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          resultTapes, encodeWord, Ne.symm h34, counterEmpty]
      · simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          copied, multiplied, resultTapes, hk3, hk4]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .finish), ((ambient, ()), none), added⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) added) = _
    rw [atLabels .finish]
    have hcfg := congrArg (fun tapes => some (⟨exit, ((ambient, ()), none), tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
    cases exit <;> simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using hcfg
  rw [show steps radix acc digit =
      1 + ((digit + 1) + (2 * (digit + 2) + MachineUnaryMultiply.steps radix acc)) by
        unfold steps MachineUnaryMultiply.steps; ring]
  rw [Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ (digit + 1),
    Function.iterate_add_apply _ (2 * (digit + 2)), hmul, hcopy, hadd]
  exact hfinish

def radixStepInTime (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩)
      (steps radix acc digit) where
  steps := steps radix acc digit
  evals_in_steps := radixStepTrace slots labels exit p atLabels base radix acc digit
    operandRadix operandAcc operandDigit counterEmpty scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 11 * Polynomial.X + Polynomial.C 13

theorem steps_le_timePolynomial (radix acc digit : ℕ) :
    steps radix acc digit ≤ timePolynomial.eval (radix + acc + digit + 3) := by
  have hr : radix ≤ radix + acc + digit + 3 := by omega
  have ha : acc ≤ radix + acc + digit + 3 := by omega
  have hd : digit ≤ radix + acc + digit + 3 := by omega
  have hprod := Nat.mul_le_mul hr ha
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

theorem programTrace (slots : Fin 6 ↪ K) (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program (σ := σ) slots)))^[steps radix acc digit]
      (some ⟨some (.multiply .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ :=
  radixStepTrace slots id none (program slots) (fun _ => rfl) base radix acc digit
    operandRadix operandAcc operandDigit counterEmpty scratchEmpty ambient register

def programInPolynomialTime (slots : Fin 6 ↪ K) (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots))
      ⟨some (.multiply .copyDrain), ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩)
      (timePolynomial.eval
        ((encodeWord radix).length + (encodeWord acc).length + (encodeWord digit).length)) where
  steps := steps radix acc digit
  evals_in_steps := programTrace slots base radix acc digit operandRadix operandAcc operandDigit
    counterEmpty scratchEmpty ambient register
  steps_le_m := by
    have hlength : (encodeWord radix).length + (encodeWord acc).length + (encodeWord digit).length =
        radix + acc + digit + 3 := by
      simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [hlength]
    exact steps_le_timePolynomial radix acc digit

end BinPackingGames.Foundations.Complexity.MachineRadixStep

namespace BinPackingGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Layout (width : Nat) := Fin 6 ⊕ Fin width
abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineRadixStep.State σ

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

def accumulator (flip : Bool) : Fin 6 := if flip then 2 else 1

@[simp] theorem accumulator_ne (flip : Bool) : accumulator flip ≠ accumulator (!flip) := by
  cases flip <;> decide

def radixLayout (flip : Bool) (i : Fin width) : Fin 6 ↪ Layout width where
  toFun
    | 0 => .inl 0
    | 1 => .inl (accumulator flip)
    | 2 => .inr i
    | 3 => .inl (accumulator (!flip))
    | 4 => .inl 4
    | 5 => .inl 5
  inj' := by
    intro a b h
    cases flip <;> fin_cases a <;> fin_cases b <;> simp [accumulator] at h ⊢

def radixSlots (slots : Layout width ↪ K) (i : Fin width) : Fin 6 ↪ K :=
  (radixLayout (parity i.val) i).trans slots

@[simp] theorem radixSlots_base (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 0 = slots (.inl 0) := rfl
@[simp] theorem radixSlots_acc (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 1 = slots (.inl (accumulator (parity i.val))) := rfl
@[simp] theorem radixSlots_digit (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 2 = slots (.inr i) := rfl
@[simp] theorem radixSlots_out (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 3 = slots (.inl (accumulator (parity (i.val + 1)))) := rfl
@[simp] theorem radixSlots_counter (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 4 = slots (.inl 4) := rfl
@[simp] theorem radixSlots_scratch (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 5 = slots (.inl 5) := rfl

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

def drainLoop (tape : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .pop tape (fun state bit => (state.1, bit))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt tape exit)))

variable [DecidableEq K]

def statement (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots (.inl 1)) (fun _ => false)
      (.load (fun state => (state.1, none)) (.goto fun _ => labels (entryLabel width 0)))
  | .radix i inner => MachineRadixStep.statement (radixSlots slots i)
      (fun l => labels (.radix i l)) (some (labels (.clear i))) inner
  | .clear i => drainLoop (slots (.inl (accumulator (parity i.val))))
      (labels (.clear i)) (some (labels (entryLabel width (i.val + 1))))
  | .finishDrain => Reduction.MachineTransfer.loopAt
      (slots (.inl (accumulator (parity width)))) (slots (.inl 5)) id false
      (labels .finishDrain) (some (labels .finishRestore))
  | .finishRestore => Reduction.MachineTransfer.loopAt (slots (.inl 5)) (slots (.inl 3)) id false
      (labels .finishRestore) exit

def program (slots : Layout width ↪ K) :
    Label width → TM2.Stmt (Alphabet (K := K)) (Label width) (State σ) := statement slots id none

def machine (width : Nat) : FinTM2 where
  K := Layout width
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := Label width
  main := .start
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Layout width))

def value (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => radix * value radix digits n + digits n

def stepCost (radix acc digit : Nat) : Nat :=
  MachineRadixStep.steps radix acc digit + acc + 1

def prefixSteps (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n)

def stageTapes (slots : Layout width ↪ K) (base : K → List Bool) (n acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl (accumulator (parity n)))) (encodeWord acc)

def resultTapes (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl 3)) (encodeWord acc ++ base (slots (.inl 3)))

theorem drainTrace (tape : K) (loopLabel : Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLoop : p loopLabel = drainLoop tape loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[n + 1]
      (some ⟨some loopLabel, ((ambient, ()), register),
        Function.update base tape (encodeWord n ++ suffix)⟩) =
      some ⟨exit, ((ambient, ()), none), Function.update base tape suffix⟩ := by
  induction n generalizing register with
  | zero =>
    change some (TM2.stepAux (p loopLabel) _ _) = _
    rw [atLoop]
    cases exit <;> simp [drainLoop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[n + 1]
      (some (TM2.stepAux (p loopLabel) _ _)) = _
    rw [atLoop]
    simp only [drainLoop, TM2.stepAux, Function.update_self, encodeWord,
      List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
      Option.getD_some, Function.update_idem]
    exact ih (some true)

structure Clean (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  accA : base (slots (.inl 1)) = []
  accB : base (slots (.inl 2)) = []
  counter : base (slots (.inl 4)) = []
  scratch : base (slots (.inl 5)) = []

omit [DecidableEq K] in
theorem Clean.acc {slots : Layout width ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (flip : Bool) : base (slots (.inl (accumulator flip))) = [] := by
  cases flip
  · exact clean.accA
  · exact clean.accB

theorem digitTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : Nat) (i : Fin width)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigit : base (slots (.inr i)) = encodeWord digit)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[stepCost radix acc digit]
      (some ⟨some (labels (.radix i (.multiply .copyDrain))), ((ambient, ()), register),
        stageTapes slots base i.val acc⟩) =
      some ⟨some (labels (entryLabel width (i.val + 1))), ((ambient, ()), none),
        stageTapes slots base (i.val + 1) (radix * acc + digit)⟩ := by
  let rs := radixSlots slots i
  let before := stageTapes slots base i.val acc
  let after := MachineRadixStep.resultTapes rs before (radix * acc + digit)
  have h01 : rs 0 ≠ rs 1 := rs.injective.ne (by decide)
  have h21 : rs 2 ≠ rs 1 := rs.injective.ne (by decide)
  have h31 : rs 3 ≠ rs 1 := rs.injective.ne (by decide)
  have h41 : rs 4 ≠ rs 1 := rs.injective.ne (by decide)
  have h51 : rs 5 ≠ rs 1 := rs.injective.ne (by decide)
  have hb : before (rs 0) = encodeWord radix := by
    change Function.update base (rs 1) (encodeWord acc) (rs 0) = _
    rw [Function.update_of_ne h01]
    exact operandRadix
  have ha : before (rs 1) = encodeWord acc := by
    exact Function.update_self _ _ _
  have hd : before (rs 2) = encodeWord digit := by
    change Function.update base (rs 1) (encodeWord acc) (rs 2) = _
    rw [Function.update_of_ne h21]
    exact operandDigit
  have hc : before (rs 4) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 4) = _
    rw [Function.update_of_ne h41]
    exact clean.counter
  have hs : before (rs 5) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 5) = _
    rw [Function.update_of_ne h51]
    exact clean.scratch
  have hout : before (rs 3) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 3) = _
    rw [Function.update_of_ne h31]
    exact clean.acc _
  have hradix := MachineRadixStep.radixStepTrace rs (fun l => labels (.radix i l))
    (some (labels (.clear i))) p (fun l => atLabels (.radix i l)) before radix acc digit
    hb ha hd hc hs ambient register
  have hold : after (rs 1) = encodeWord acc := by
    change Function.update before (rs 3) _ (rs 1) = _
    rw [Function.update_of_ne (Ne.symm h31), ha]
  have hstart : Function.update after (rs 1) (encodeWord acc ++ []) = after := by
    rw [List.append_nil, ← hold, Function.update_eq_self]
  have hfinish : Function.update after (rs 1) [] =
      stageTapes slots base (i.val + 1) (radix * acc + digit) := by
    have hempty : base (rs 1) = [] := clean.acc _
    change Function.update (Function.update (Function.update base (rs 1) (encodeWord acc))
      (rs 3) (encodeWord (radix * acc + digit) ++ before (rs 3))) (rs 1) [] =
      Function.update base (rs 3) (encodeWord (radix * acc + digit))
    rw [hout, List.append_nil]
    funext k
    by_cases h1 : k = rs 1
    · subst k; simp [Ne.symm h31, hempty]
    · by_cases h3 : k = rs 3
      · subst k; simp [h31]
      · simp [h1, h3]
  have hdrain := drainTrace (rs 1) (labels (.clear i))
    (some (labels (entryLabel width (i.val + 1)))) p (atLabels (.clear i))
    after acc [] ambient none
  rw [hstart, hfinish] at hdrain
  rw [show stepCost radix acc digit = (acc + 1) + MachineRadixStep.steps radix acc digit by
    unfold stepCost; omega, Function.iterate_add_apply, hradix]
  exact hdrain

theorem prefixTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (n : Nat) (hn : n ≤ width) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps radix digits n]
      (some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩) =
      some ⟨some (labels (entryLabel width n)), ((ambient, ()), none),
        stageTapes slots base n (value radix digits n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < width := by omega
    let i : Fin width := ⟨n, hlt⟩
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    have h := digitTrace slots labels exit p atLabels base radix (value radix digits n)
      (digits n) i operandRadix (operandDigits i) clean ambient none
    simpa only [entryLabel, dite_eq_left hlt, i, value] using h

theorem finishTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (acc : Nat) (clean : Clean slots base) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[2 * acc + 4]
      (some ⟨some (labels .finishDrain), ((ambient, ()), none), stageTapes slots base width acc⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ := by
  let src := slots (.inl (accumulator (parity width)))
  let scratch := slots (.inl 5)
  let dst := slots (.inl 3)
  have hsrcScratch : src ≠ scratch := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hsrcDst : src ≠ dst := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hscratchDst : scratch ≠ dst := slots.injective.ne (by simp)
  have hsrc : base src = [] := clean.acc _
  have hs : base scratch = [] := clean.scratch
  let before := stageTapes slots base width acc
  let middle := Function.update base scratch (encodeWord acc).reverse
  have hinput : before src = encodeWord acc := Function.update_self _ _ _
  have hscratch : before scratch = [] := by
    change Function.update base src (encodeWord acc) scratch = []
    rw [Function.update_of_ne (Ne.symm hsrcScratch), hs]
  have hfirstTapes : Reduction.MachineTransfer.tapesAt src scratch before []
      ((before src).reverse.map id ++ before scratch) = middle := by
    rw [hinput, hscratch, List.append_nil, List.map_id]
    funext k
    by_cases h1 : k = src
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, middle, hsrcScratch, hsrc]
    · by_cases h2 : k = scratch
      · subst k; simp [Reduction.MachineTransfer.tapesAt, middle]
      · simp [Reduction.MachineTransfer.tapesAt, middle, before, stageTapes, h1, h2, src]
  have first := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) src scratch hsrcScratch id false
    (labels .finishDrain) (some (labels .finishRestore)) p (atLabels .finishDrain)
    before (ambient, ()) none
  rw [hfirstTapes] at first
  have hlength : (before src).length + 1 = acc + 2 := by
    simp [hinput, encodeWord, Nat.add_assoc]
  rw [hlength] at first
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishDrain), ((ambient, ()), none), before⟩) =
      some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩ at first
  have hmSource : middle scratch = (encodeWord acc).reverse := Function.update_self _ _ _
  have hmOutput : middle dst = base dst := by
    exact Function.update_of_ne (Ne.symm hscratchDst) _ _
  have hsecondTapes : Reduction.MachineTransfer.tapesAt scratch dst middle []
      ((middle scratch).reverse.map id ++ middle dst) = resultTapes slots base acc := by
    rw [hmSource, hmOutput, List.reverse_reverse, List.map_id]
    funext k
    by_cases h1 : k = dst
    · subst k; simp [Reduction.MachineTransfer.tapesAt, resultTapes, dst]
    · by_cases h2 : k = scratch
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, hscratchDst, hs, scratch, dst]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, h1, h2, dst]
  have second := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) scratch dst hscratchDst id false
    (labels .finishRestore) exit p (atLabels .finishRestore) middle (ambient, ()) none
  rw [hsecondTapes] at second
  have hmLength : (middle scratch).length + 1 = acc + 2 := by
    simp [hmSource, encodeWord, Nat.add_assoc]
  rw [hmLength] at second
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ at second
  rw [show 2 * acc + 4 = (acc + 2) + (acc + 2) by omega,
    Function.iterate_add_apply, first]
  exact second

def steps (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  prefixSteps radix digits width + 2 * value radix digits width + 5

theorem hornerTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix digits width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩ := by
  have start : TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩ =
      some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩ := by
    change some (TM2.stepAux (p (labels .start)) _ _) = _
    rw [atLabels .start]
    simp only [statement, TM2.stepAux, clean.accA, stageTapes, parity, accumulator,
      Bool.false_eq_true, ↓reduceIte, encodeWord, List.replicate_zero, List.nil_append]
  have prefixRun := prefixTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient width (Nat.le_refl _)
  have final := finishTrace slots labels exit p atLabels base (value radix digits width) clean ambient
  have hend : entryLabel width width = .finishDrain := by simp [entryLabel]
  rw [hend] at prefixRun
  rw [show steps radix digits width =
    ((2 * value radix digits width + 4) + prefixSteps radix digits width) + 1 by
      unfold steps; omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    (2 * value radix digits width + 4) + prefixSteps radix digits width]
      (TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩) = _
  rw [start, Function.iterate_add_apply, prefixRun]
  exact final

omit [DecidableEq K] in
theorem value_eq_foldl (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    value radix digits n =
      ((List.range n).map digits).foldl (fun acc digit => radix * acc + digit) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, ← ih]

omit [DecidableEq K] in

theorem value_add_one_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n + 1 ≤ (magnitude + 1) ^ n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    have hn' : n < width := by omega
    have hm := Nat.mul_le_mul_right (value radix digits n) radixBound
    calc
      value radix digits (n + 1) + 1 ≤ (magnitude + 1) * (value radix digits n + 1) := by
        rw [value]
        have hd := digitBound n hn'
        nlinarith
      _ ≤ (magnitude + 1) * (magnitude + 1) ^ n :=
        Nat.mul_le_mul_left _ (ih (by omega))
      _ = (magnitude + 1) ^ (n + 1) := by rw [pow_succ]; ac_rfl

omit [DecidableEq K] in
theorem value_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n ≤ (magnitude + 1) ^ width := by
  have h := value_add_one_le radix digits width magnitude radixBound digitBound n hn
  exact (Nat.le_trans (Nat.le_add_right _ _) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) hn)

def perDigitBound (width magnitude : Nat) : Nat :=
  3 * magnitude * (magnitude + 1) ^ width + 9 * (magnitude + 1) ^ width + 3 * magnitude + 14

omit [DecidableEq K] in
theorem stepCost_le (radix acc digit width magnitude : Nat)
    (radixBound : radix ≤ magnitude) (accBound : acc ≤ (magnitude + 1) ^ width)
    (digitBound : digit ≤ magnitude) :
    stepCost radix acc digit ≤ perDigitBound width magnitude := by
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 3 radixBound) accBound
  unfold stepCost MachineRadixStep.steps perDigitBound
  omega

omit [DecidableEq K] in
theorem prefixSteps_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) :
    prefixSteps radix digits n ≤ n * perDigitBound width magnitude := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hn' : n < width := by omega
    have ha := value_le radix digits width magnitude radixBound digitBound n (by omega)
    have hc := stepCost_le radix (value radix digits n) (digits n) width magnitude
      radixBound ha (digitBound n hn')
    rw [prefixSteps]
    calc
      prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n) ≤
          n * perDigitBound width magnitude + perDigitBound width magnitude :=
        Nat.add_le_add (ih (by omega)) hc
      _ = (n + 1) * perDigitBound width magnitude := by rw [Nat.add_mul, Nat.one_mul]

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width *
    (3 * Polynomial.X * (Polynomial.X + 1) ^ width +
      9 * (Polynomial.X + 1) ^ width + 3 * Polynomial.X + 14) +
    2 * (Polynomial.X + 1) ^ width + 5

omit [DecidableEq K] in
@[simp] theorem timePolynomial_eval (width magnitude : Nat) :
    (timePolynomial width).eval magnitude =
      width * perDigitBound width magnitude + 2 * (magnitude + 1) ^ width + 5 := by
  simp [timePolynomial, perDigitBound]

omit [DecidableEq K] in
theorem steps_le_timePolynomial (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    steps radix digits width ≤ (timePolynomial width).eval magnitude := by
  have hp := prefixSteps_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have hv := value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  rw [timePolynomial_eval]
  unfold steps
  omega

def hornerInTime (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩)
      (steps radix digits width) where
  steps := steps radix digits width
  evals_in_steps := hornerTrace slots labels exit p atLabels base radix digits
    operandRadix operandDigits clean ambient register
  steps_le_m := Nat.le_refl _

def hornerInPolynomialTime (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) (magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩)
      ((timePolynomial width).eval magnitude) where
  steps := steps radix digits width
  evals_in_steps := hornerTrace slots labels exit p atLabels base radix digits
    operandRadix operandDigits clean ambient register
  steps_le_m := steps_le_timePolynomial radix digits width magnitude radixBound digitBound

open scoped BigOperators

def operandLength (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  (encodeWord radix).length + ∑ i ∈ Finset.range width, (encodeWord (digits i)).length

omit [DecidableEq K] in
theorem radix_le_operandLength (radix : Nat) (digits : Nat → Nat) (width : Nat) :
    radix ≤ operandLength radix digits width := by
  unfold operandLength
  simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
  omega

omit [DecidableEq K] in
theorem digit_le_operandLength (radix : Nat) (digits : Nat → Nat) (width i : Nat)
    (hi : i < width) : digits i ≤ operandLength radix digits width := by
  have h : (encodeWord (digits i)).length ≤
      ∑ j ∈ Finset.range width, (encodeWord (digits j)).length :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((encodeWord (digits j)).length))
      (Finset.mem_range.mpr hi)
  have hlen : digits i + 1 ≤ ∑ j ∈ Finset.range width, (encodeWord (digits j)).length := by
    simpa only [encodeWord, List.length_append, List.length_replicate, List.length_singleton] using h
  unfold operandLength
  omega

@[simp] theorem resultTapes_output (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) :
    resultTapes slots base acc (slots (.inl 3)) = encodeWord acc ++ base (slots (.inl 3)) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat)
    (k : K) (hk : k ≠ slots (.inl 3)) : resultTapes slots base acc k = base k := by
  simp [resultTapes, hk]

def hornerInEncodedPolynomialTime (slots : Layout width ↪ K) (labels : Label width → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩)
      ((timePolynomial width).eval (operandLength radix digits width)) :=
  hornerInPolynomialTime slots labels exit p atLabels base radix digits operandRadix operandDigits
    clean ambient register (operandLength radix digits width)
    (radix_le_operandLength radix digits width)
    (fun i hi => digit_le_operandLength radix digits width i hi)

end BinPackingGames.Foundations.Complexity.MachineHorner

end OAI
