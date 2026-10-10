import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Machines.MachineAppendAt
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.PCP.GraphTables
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

/-- The homogeneous parts of a finite machine, without dependent alphabet casts. -/
structure Program (K Λ σ : Type) where
  input : K
  output : K
  main : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

section Structural

variable {K Λ Λ' σ : Type} [DecidableEq K]

def extendedLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def extendedCfg (labels : Λ → Λ') (haltTarget : Option Λ') (register : Option Bool)
    (cfg : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ' (σ × Option Bool) :=
  ⟨extendedLabel labels haltTarget cfg.l, (cfg.var, register), cfg.stk⟩

/-- Add one finite scratch register while preserving each raw transition. -/
def extendedStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ →
      TM2.Stmt (fun _ : K => Bool) Λ' (σ × Option Bool)
  | .push k f next => .push k (fun state => f state.1)
      (extendedStmt labels haltTarget next)
  | .peek k f next => .peek k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .pop k f next => .pop k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .load f next => .load (fun state => (f state.1, state.2))
      (extendedStmt labels haltTarget next)
  | .branch test yes no => .branch (fun state => test state.1)
      (extendedStmt labels haltTarget yes) (extendedStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_extended (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ)
    (register : Option Bool) (tapes : K → List Bool) :
    TM2.stepAux (extendedStmt labels haltTarget stmt) (state, register) tapes =
      extendedCfg labels haltTarget register (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Structural

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def sourceMachine (P : Program K Λ σ) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Λ
  main := P.main
  σ := σ
  initialState := P.initial
  m := P.code

abbrev Label (Λ : Type) (chosen : List K) := Λ ⊕ (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (chosen : List K) : MachineDrainMany.Label chosen → Label Λ chosen :=
  fun label => .inr (.inl label)

def resetLabel (chosen : List K) : Label Λ chosen := .inr (.inr ())

def cleanupEntry (chosen : List K) : Option (Label Λ chosen) :=
  MachineDrainMany.entry chosen (cleanupLabel chosen) (some (resetLabel chosen))

def completedProgram (P : Program K Λ σ) (chosen : List K) :
    Label Λ chosen → TM2.Stmt (fun _ : K => Bool) (Label Λ chosen) (σ × Option Bool)
  | .inl label => extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) label
  | .inr (.inr _) => .load (fun _ => (P.initial, none)) .halt

/-- A fixed finite program over the same Boolean tapes as the raw machine. -/
def completedMachine (P : Program K Λ σ) (chosen : List K) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Label Λ chosen
  main := .inl P.main
  σ := σ × Option Bool
  initialState := (P.initial, none)
  m := completedProgram P chosen

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

def embeddedCfg (P : Program K Λ σ) (chosen : List K)
    (cfg : (sourceMachine P).Cfg) : (completedMachine P chosen).Cfg :=
  extendedCfg Sum.inl (cleanupEntry chosen) none cfg

theorem step_simulation (P : Program K Λ σ) (chosen : List K)
    (a b : (sourceMachine P).Cfg) (step : (sourceMachine P).step a = some b) :
    (completedMachine P chosen).step (embeddedCfg P chosen a) =
      some (embeddedCfg P chosen b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (P.code label) state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)) (state, none) tapes) = _
      erw [stepAux_extended]
      rfl

@[simp] theorem embedded_init (P : Program K Λ σ) (chosen : List K) (input : List Bool) :
    embeddedCfg P chosen (initList (sourceMachine P) input) =
      initList (completedMachine P chosen) input := rfl

omit [Fintype K] [Fintype Λ] [Fintype σ] in
theorem finalTapes_eq (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (base : K → List Bool) :
    MachineDrainMany.finalTapes chosen base =
      MachineDrainMany.haltTapes P.output (base P.output) := by
  funext k
  rw [MachineDrainMany.finalTapes_apply]
  by_cases h : k = P.output
  · subst k
    simp [MachineDrainMany.haltTapes, complete]
  · simp [MachineDrainMany.haltTapes, complete, h]

theorem haltList_eq (P : Program K Λ σ) (chosen : List K) (output : List Bool) :
    haltList (completedMachine P chosen) output =
      ⟨none, (P.initial, none), MachineDrainMany.haltTapes P.output output⟩ := by
  congr 1

/-- The cleanup path consists of actual drains and one physical state reset. -/
def cleanupExecution (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (state : σ)
    (register : Option Bool) (base : K → List Bool) :
    StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩
      (some (haltList (completedMachine P chosen) (base P.output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine P chosen).Cfg :=
    ⟨some (resetLabel chosen), (state, MachineDrainMany.finalRegister chosen register),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) (completedProgram P chosen) (fun _ => rfl) base state register
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine P chosen).step
      after (some (haltList (completedMachine P chosen) (base P.output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (P.initial, none), MachineDrainMany.finalTapes chosen base⟩ :
          (completedMachine P chosen).Cfg) =
        some (haltList (completedMachine P chosen) (base P.output))
      erw [finalTapes_eq P chosen complete, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

/-- No assumption about cleanup execution or clean raw work tapes is required. -/
def outputsInTime (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (input output : List Bool) (state : σ) (base : K → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime (sourceMachine P).step
      (initList (sourceMachine P) input) (some ⟨none, state, base⟩) budget)
    (correctOutput : base P.output = output) :
    TM2OutputsInTime (completedMachine P chosen) input (some output)
      (budget + chosen.length *
        (input.length + budget * Runtime.programPushBound (sourceMachine P) + 1) + 1) := by
  let lifted := liftExecutionInTime (sourceMachine P).step
    (completedMachine P chosen).step (embeddedCfg P chosen) (step_simulation P chosen) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution P chosen complete state none base)
  have stackBound : ∀ k, (base k).length ≤
      input.length + budget * Runtime.programPushBound (sourceMachine P) := by
    intro k
    have h := Runtime.executionSizeBound (sourceMachine P).step
      (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (sourceMachine P))
      (Runtime.stepStackLength (sourceMachine P) k) raw
    exact h.trans (Nat.add_le_add_right (Runtime.initialStackLength (sourceMachine P) input k) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

noncomputable def completedTime (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C chosen.length *
    (Polynomial.X + rawTime * Polynomial.C (Runtime.programPushBound (sourceMachine P)) + 1) + 1

theorem completedTime_eval (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime P chosen rawTime).eval n =
      rawTime.eval n + chosen.length *
        (n + rawTime.eval n * Runtime.programPushBound (sourceMachine P) + 1) + 1 := by
  simp [completedTime]

/-- An actual raw terminal execution, with arbitrary remaining state and tapes. -/
structure TerminalRun (P : Program K Λ σ) (input output : List Bool) (budget : Nat) where
  state : σ
  tapes : K → List Bool
  execution : StateTransition.EvalsToInTime (sourceMachine P).step
    (initList (sourceMachine P) input) (some ⟨none, state, tapes⟩) budget
  output_eq : tapes P.output = output

/-- A polynomial raw run becomes a full canonical-output computation certificate. -/
noncomputable def computableInPolyTime {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    TM2ComputableInPolyTime encodeIn encodeOut f where
  tm := completedMachine P chosen
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := completedTime P chosen rawTime
  outputsFun a := by
    change TM2OutputsInTime (completedMachine P chosen) ((encodeIn a).map id)
      (some ((encodeOut (f a)).map id)) ((completedTime P chosen rawTime).eval _)
    erw [List.map_id, List.map_id, completedTime_eval]
    exact outputsInTime P chosen complete _ _ (run a).state (run a).tapes _
      (run a).execution (run a).output_eq

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

/-- An explicit finite enumeration supplies the fixed cleanup list. -/
noncomputable def computableInPolyTimeOfEnumeration {α β : Type} {N : Nat}
    (P : Program K Λ σ) (enumeration : Fin N ≃ K)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    TM2ComputableInPolyTime encodeIn encodeOut f :=
  computableInPolyTime P (MachineDrainMany.workTapes enumeration P.output)
    (fun k => MachineDrainMany.mem_workTapes enumeration P.output k)
    encodeIn encodeOut f rawTime run

end UniqueGamesTheorem.Foundations.Complexity.MachineCanonicalOutput

namespace UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.relationRead, .relationRestore, .reverseRead,
  .reverseRestore, .tailRead, .tailRestore, .appendOld, .appendRow, .appendBack]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- `fields 0`, `fields 1`, and `fields 2` are the tail, reverse index, and
encoded relation tapes. Every instruction reads or writes a single tape head. -/
def routine (fields : Fin 3 → K) (row output scratch : K)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .relationRead => Reduction.MachineTransfer.loopAt (fields 2) scratch id false
      (labels .relationRead) (some (labels .relationRestore))
  | .relationRestore => MachineCopy.forkLoop scratch (fields 2) row false
      (labels .relationRestore) (some (labels .reverseRead))
  | .reverseRead => Reduction.MachineTransfer.loopAt (fields 1) scratch id false
      (labels .reverseRead) (some (labels .reverseRestore))
  | .reverseRestore => MachineCopy.forkLoop scratch (fields 1) row false
      (labels .reverseRestore) (some (labels .tailRead))
  | .tailRead => Reduction.MachineTransfer.loopAt (fields 0) scratch id false
      (labels .tailRead) (some (labels .tailRestore))
  | .tailRestore => MachineCopy.forkLoop scratch (fields 0) row false
      (labels .tailRestore) (some (labels .appendOld))
  | .appendOld => Reduction.MachineTransfer.loopAt output scratch id false
      (labels .appendOld) (some (labels .appendRow))
  | .appendRow => Reduction.MachineTransfer.loopAt row scratch id false
      (labels .appendRow) (some (labels .appendBack))
  | .appendBack => Reduction.MachineTransfer.loopAt scratch output id false
      (labels .appendBack) exit

/-- Exact row field concatenation at the level of stored bits. -/
def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

/-- The three actual preserving-copy phases, with exact tape handoffs. -/
theorem prefixTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowScratch : row ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * (fieldSize fields base + 3)]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨some (labels .appendOld), (ambient, none), prefixTapes fields row base⟩ := by
  let afterRelation := Function.update base row (base (fields 2) ++ base row)
  let afterReverse := Function.update afterRelation row
    (base (fields 1) ++ afterRelation row)
  have hfirst := MachineCopy.copyTrace (fields 2) row scratch
    (hfields 2).1 (hfields 2).2 hrowScratch false
    (labels .relationRead) (labels .relationRestore) (some (labels .reverseRead))
    program (hprogram .relationRead) (hprogram .relationRestore) base hscratch ambient register
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 2)).length + 1)]
    (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
    some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩ at hfirst
  have hsecond := MachineCopy.copyTrace (fields 1) row scratch
    (hfields 1).1 (hfields 1).2 hrowScratch false
    (labels .reverseRead) (labels .reverseRestore) (some (labels .tailRead))
    program (hprogram .reverseRead) (hprogram .reverseRestore) afterRelation
    (by simp [afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have hrev : afterRelation (fields 1) = base (fields 1) := by
    simp [afterRelation, (hfields 1).1]
  rw [hrev] at hsecond
  change (MachineComposition.advance (TM2.step program))^[2 * ((base (fields 1)).length + 1)]
    (some ⟨some (labels .reverseRead), (ambient, none), afterRelation⟩) =
    some ⟨some (labels .tailRead), (ambient, none), afterReverse⟩ at hsecond
  have hthird := MachineCopy.copyTrace (fields 0) row scratch
    (hfields 0).1 (hfields 0).2 hrowScratch false
    (labels .tailRead) (labels .tailRestore) (some (labels .appendOld))
    program (hprogram .tailRead) (hprogram .tailRestore) afterReverse
    (by simp [afterReverse, afterRelation, Ne.symm hrowScratch, hscratch]) ambient none
  have htail : afterReverse (fields 0) = base (fields 0) := by
    simp [afterReverse, afterRelation, (hfields 0).1]
  rw [htail] at hthird
  have hfinal : Function.update afterReverse row
      (base (fields 0) ++ afterReverse row) = prefixTapes fields row base := by
    simp [afterReverse, afterRelation, prefixTapes, fieldBits, List.append_assoc]
  rw [hfinal] at hthird
  rw [show 2 * (fieldSize fields base + 3) =
    2 * ((base (fields 0)).length + 1) +
      (2 * ((base (fields 1)).length + 1) + 2 * ((base (fields 2)).length + 1)) by
        simp only [fieldSize]; omega,
    Function.iterate_add_apply,
    Function.iterate_add_apply (m := 2 * ((base (fields 1)).length + 1))
      (n := 2 * ((base (fields 2)).length + 1)), hfirst, hsecond]
  exact hthird

theorem appendTrace (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[
        4 * fieldSize fields base + 2 * (base output).length + 9]
      (some ⟨some (labels .relationRead), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base output (base output ++ fieldBits fields base)⟩ := by
  have hprefix := prefixTrace fields row output scratch hfields hrowScratch
    labels exit program hprogram base hscratch ambient register
  have happend := MachineAppendAt.appendTrace row output scratch hrowOutput hrowScratch
    houtputScratch false (labels .appendOld) (labels .appendRow) (labels .appendBack)
    exit program (hprogram .appendOld) (hprogram .appendRow) (hprogram .appendBack)
    (prefixTapes fields row base)
    (by simp [prefixTapes, Ne.symm hrowScratch, hscratch]) ambient none
  have hrowbits : prefixTapes fields row base row = fieldBits fields base := by
    simp [prefixTapes, hrow]
  have hout : prefixTapes fields row base output = base output := by
    simp [prefixTapes, Ne.symm hrowOutput]
  rw [hrowbits, hout, fieldBits_length] at happend
  have hfinal : MachineAppendAt.appendTapes row output (prefixTapes fields row base) =
      Function.update base output (base output ++ fieldBits fields base) := by
    funext k
    by_cases ho : k = output
    · subst k
      simp [MachineAppendAt.appendTapes, hrowbits, hout]
    · by_cases hr : k = row
      · subst k
        simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, hrowOutput, hrow]
      · simp [MachineAppendAt.appendTapes, Reduction.MachineTransfer.tapesAt,
          prefixTapes, ho, hr]
  rw [hfinal] at happend
  rw [show 4 * fieldSize fields base + 2 * (base output).length + 9 =
      (2 * (fieldSize fields base + (base output).length) + 3) +
        2 * (fieldSize fields base + 3) by omega,
    Function.iterate_add_apply, hprefix]
  exact happend

/-- The full existing graph codec, including all 4096 unary predicate fields. -/
theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

omit [DecidableEq K] in
theorem fieldBits_eq_rowBits {n m : Nat} (r : DartRow n m)
    (fields : Fin 3 → K) (base : K → List Bool)
    (htail : base (fields 0) = encodeWord r.tail.val)
    (hreverse : base (fields 1) = encodeWord r.reverseIndex.val)
    (hrelation : base (fields 2) = encodeWords (relationWords r.relation)) :
    fieldBits fields base = encodeWords (rowWords r) := by
  rw [fieldBits, htail, hreverse, hrelation, rowBits_eq]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 9

omit [DecidableEq K] in
theorem timePolynomial_bounds (fields : Fin 3 → K) (base : K → List Bool) (output : K) :
    4 * fieldSize fields base + 2 * (base output).length + 9 ≤
      timePolynomial.eval (fieldSize fields base + (base output).length) := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  omega

/-- A composable actual execution certificate for a correctly encoded row.
The program is fixed; row data occur only in the input-tape equalities. -/
def rowAppendInTime {n m : Nat} (r : DartRow n m)
    (fields : Fin 3 → K) (row output scratch : K)
    (hfields : ∀ i, fields i ≠ row ∧ fields i ≠ scratch)
    (hrowOutput : row ≠ output) (hrowScratch : row ≠ scratch)
    (houtputScratch : output ≠ scratch) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (hprogram : ∀ label, program (labels label) = routine fields row output scratch labels exit label)
    (base : K → List Bool) (hrow : base row = []) (hscratch : base scratch = [])
    (htail : base (fields 0) = encodeWord r.tail.val)
    (hreverse : base (fields 1) = encodeWord r.reverseIndex.val)
    (hrelation : base (fields 2) = encodeWords (relationWords r.relation))
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .relationRead), (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base output (base output ++ encodeWords (rowWords r))⟩)
      (timePolynomial.eval (fieldSize fields base + (base output).length)) where
  steps := 4 * fieldSize fields base + 2 * (base output).length + 9
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[_] _ = _
    rw [← fieldBits_eq_rowBits r fields base htail hreverse hrelation]
    exact appendTrace fields row output scratch hfields hrowOutput hrowScratch
      houtputScratch labels exit program hprogram base hrow hscratch ambient register
  steps_le_m := timePolynomial_bounds fields base output

/-- A fixed nine-label six-stack finite machine implementing the routine.
Its inputs may be supplied in a caller's distributed tape configuration. -/
def machine : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := .relationRead
  σ := Unit × Option Bool
  initialState := ((), none)
  m := routine (fun i : Fin 3 => i.castLE (by decide)) 3 4 5 id none

/-- Direct execution of the concrete finite machine on caller-supplied unary
fields. This instantiates all program equations; no execution premise remains. -/
def machineRowInTime {n m : Nat} (r : DartRow n m) (base : Fin 6 → List Bool)
    (hrow : base 3 = []) (hscratch : base 5 = [])
    (htail : base 0 = encodeWord r.tail.val)
    (hreverse : base 1 = encodeWord r.reverseIndex.val)
    (hrelation : base 2 = encodeWords (relationWords r.relation)) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .relationRead, ((), register), base⟩
      (some ⟨none, ((), none),
        Function.update base (4 : Fin 6) (base 4 ++ encodeWords (rowWords r))⟩)
      (timePolynomial.eval ((encodeWords (rowWords r)).length + (base 4).length)) := by
  let fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)
  have hfields (i : Fin 3) : fields i ≠ 3 ∧ fields i ≠ 5 := by
    constructor
    · intro h
      have he := congrArg Fin.val h
      change i.val = 3 at he
      omega
    · intro h
      have he := congrArg Fin.val h
      change i.val = 5 at he
      omega
  have hsize : fieldSize fields base = (encodeWords (rowWords r)).length := by
    rw [← fieldBits_length, fieldBits_eq_rowBits r fields base htail hreverse hrelation]
  have run := rowAppendInTime r fields (3 : Fin 6) 4 5 hfields (by decide) (by decide)
    (by decide) id none machine.m (fun _ => rfl) base hrow hscratch
    htail hreverse hrelation () register
  rw [hsize] at run
  convert run using 1
  rfl

theorem outputFrame (base : K → List Bool) (output k : K) (hk : k ≠ output)
    (bits : List Bool) :
    Function.update base output (base output ++ bits) k = base k := by
  simp [hk]

end UniqueGamesTheorem.Foundations.Complexity.MachineTableRows

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

/-- The actual 64-by-64 always-accepting relation. -/
def trueRelation : RelationTable := Vector.replicate 4096 true

def trueBits : List Bool := encodeWords (relationWords trueRelation)

theorem trueBits_length : trueBits.length = 8192 := by
  simp only [trueBits, encodeWords_length, relationWords, trueRelation,
    Vector.toList_replicate, List.map_replicate, List.sum_replicate_nat,
    List.length_replicate]
  rfl

def rowBits (v e : Nat) : List Bool := encodeWord v ++ encodeWord e ++ trueBits

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

/-- Ordered serialized rows with successive physically stored reverse indices. -/
def rowsBits (v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => rowBits v e ++ rowsBits v (e + 1) count

/-- One initialization label and ten labels per fixed port. -/
abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

/-- The only data-changing index operation is a tape push, below. This
function chooses a finite continuation among the fixed port-control labels. -/
def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

/-- No input-dependent natural number occurs in the finite program. -/
def program (d : Nat) : Label d → TM2.Stmt Alphabet (Label d) (σ × Option Bool)
  | .inl () => pushWord 2 trueBits.reverse
      (.load (fun state => (state.1, none)) (continueAt (entry d)))
  | .inr (p, .inl stage) => MachineTableRows.routine fields 3 4 5
      (rowLabel p) (some (bumpLabel p)) stage
  | .inr (p, .inr ()) => .push 1 (fun _ => true) (continueAt (afterPort p))

/-- The three unary row fields, two empty work tapes, and accumulated output. -/
def fieldTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  ![encodeWord v, encodeWord e, trueBits, [], output, []]

/-- Before initialization, the fixed-relation tape is empty. -/
def initialTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  Function.update (fieldTapes v e output) 2 []

/-- The fixed literal relation is actually emitted by a finite push chain. -/
theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

/-- The reverse index advances by pushing a real unary bit. The delimiter,
all input fields, output, and work tapes have their exact stated contents. -/
theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

/-- The concrete row body and its actual index increment are consecutive
phases of one fixed program; no whole-body trace is supplied as a premise. -/
theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

/-- Exact sum of actual row-and-increment costs. This recurrence is matched
to the program by `suffixTrace`, rather than postulated as a runtime. -/
def steps (v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 0
  | count + 1 => (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count

/-- Actual execution from any port boundary to the final halt. The finite
control index fixes the remaining number of rows; all unbounded values are
physically stored in `fieldTapes`. -/
theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

/-- One fixed-relation initialization transition followed by all actual rows.
At zero ports initialization itself halts; no row is spuriously produced. -/
theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

/-- Actual finite graph rows in increasing reverse-index order. -/
def graphRows {n m : Nat} (v : Fin n) (e : Nat) :
    (count : Nat) → e + count ≤ m → List (DartRow n m)
  | 0, _ => []
  | count + 1, h =>
      ⟨v, ⟨e, by omega⟩, trueRelation⟩ ::
        graphRows v (e + 1) count (by omega)

theorem graphRows_length {n m : Nat} (v : Fin n) (e count : Nat) (h : e + count ≤ m) :
    (graphRows v e count h).length = count := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih => simp [graphRows, ih]

/-- The machine's bit stream is exactly the existing codec on the actual
ordered row list, including both index fields and every predicate entry. -/
theorem rowsBits_eq_graphRows {n m : Nat} (v : Fin n) (e count : Nat)
    (h : e + count ≤ m) :
    rowsBits v.val e count = encodeWords ((graphRows v e count h).flatMap rowWords) := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    simp [rowsBits, graphRows, encodeWords_append, MachineTableRows.rowBits_eq,
      rowBits, trueBits]
    exact ih (e + 1) (by omega)

/-- For one vertex of an `n`-vertex degree-`d` graph, every dummy dart is its
own reverse. The caller's initial index is the actual unary value `d * v`. -/
def dummyRows {n : Nat} (d : Nat) (v : Fin n) : List (DartRow n (n * d)) :=
  graphRows v (d * v.val) d (by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    simpa only [Nat.succ_mul, Nat.mul_comm] using h)

theorem dummyRows_length {n : Nat} (d : Nat) (v : Fin n) :
    (dummyRows d v).length = d := graphRows_length _ _ _ _

theorem dummyRowsTrace {n : Nat} (d : Nat) (v : Fin n) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v.val (d * v.val) output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v.val (d * v.val) output⟩) =
      some ⟨none, (ambient, none), fieldTapes v.val (d * v.val + d)
        (output ++ encodeWords ((dummyRows d v).flatMap rowWords))⟩ := by
  have h := allTrace d v.val (d * v.val) output ambient register
  rw [rowsBits_eq_graphRows v (d * v.val) d (by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    simpa only [Nat.succ_mul, Nat.mul_comm] using h)] at h
  exact h

/-- Every actual row cost is bounded by the largest row and accumulated
output encountered during this finite loop. -/
theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

/-- The variable-size input is exactly the two physical unary fields and
existing output. The relation field is a fixed program constant. -/
def inputSize (v e : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + output.length

/-- A linear polynomial for each fixed port count `d`. -/
noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C d *
    (Polynomial.C 4 * (Polynomial.X + Polynomial.C (d + 8192)) +
      Polynomial.C 2 * (Polynomial.X + Polynomial.C d *
        (Polynomial.X + Polynomial.C (d + 8192))) + Polynomial.C 10) + 1

theorem timePolynomial_bounds (d v e : Nat) (output : List Bool) :
    steps v e output d + 1 ≤ (timePolynomial d).eval (inputSize v e output) := by
  have h := steps_le_bound v e output d
  have hB : v + e + d + 8194 ≤ inputSize v e output + d + 8192 := by
    simp only [inputSize, encodeWord_length]
    omega
  have hO : output.length ≤ inputSize v e output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hm := Nat.mul_le_mul_left d hB
  have hinner :
      4 * (v + e + d + 8194) + 2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
      4 * (inputSize v e output + d + 8192) +
        2 * (inputSize v e output + d * (inputSize v e output + d + 8192)) + 10 := by
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hB)
      (Nat.mul_le_mul_left 2 (Nat.add_le_add hO hm))) 10
  have htotal := h.trans (Nat.mul_le_mul_left d hinner)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  simpa only [Nat.add_assoc] using Nat.add_le_add_right htotal 1

/-- A fixed finite machine. Its control stores only the fixed port position;
vertex and reverse-index values reside on the tapes. -/
def machine (d : Nat) : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label d
  main := start d
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program d

/-- The full actual finite-machine execution, including initialization and
all rows. No body trace or runtime hypothesis is an input to this certificate. -/
def machineInTime (d v e : Nat) (output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine d).step
      ⟨some (start d), ((), register), initialTapes v e output⟩
      (some ⟨none, ((), none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩)
      ((timePolynomial d).eval (inputSize v e output)) where
  steps := steps v e output d + 1
  evals_in_steps := by
    convert allTrace d v e output () register using 1
    rfl
  steps_le_m := timePolynomial_bounds d v e output

/-- The same actual machine on the padding invariant `e = d * v`, with
its exact existing-codec graph-row output. -/
def machineDummyInTime {n : Nat} (d : Nat) (v : Fin n)
    (output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine d).step
      ⟨some (start d), ((), register), initialTapes v.val (d * v.val) output⟩
      (some ⟨none, ((), none), fieldTapes v.val (d * v.val + d)
        (output ++ encodeWords ((dummyRows d v).flatMap rowWords))⟩)
      ((timePolynomial d).eval (inputSize v.val (d * v.val) output)) where
  steps := steps v.val (d * v.val) output d + 1
  evals_in_steps := by
    convert dummyRowsTrace d v output () register using 1
    rfl
  steps_le_m := timePolynomial_bounds d v.val (d * v.val) output

/-- Input tail and both work tapes retain their required contents. The
relation tape keeps the one initialized fixed field for subsequent use. -/
theorem finalFrame (v e : Nat) (output : List Bool) :
    fieldTapes v e output 0 = encodeWord v ∧
    fieldTapes v e output 2 = trueBits ∧
    fieldTapes v e output 3 = [] ∧ fieldTapes v e output 5 = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end UniqueGamesTheorem.Foundations.Complexity.MachineDummyRows

end OAI
