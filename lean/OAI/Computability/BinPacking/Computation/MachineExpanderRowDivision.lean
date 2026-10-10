import OAI.Computability.BinPacking.Computation.MachinePortReindex
import OAI.Computability.BinPacking.PCP.Emitter

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | none => exit
  | some l => some (labels l)

def configuration (labels : Λ → Λ') (exit : Option Λ') (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ := ⟨label labels exit c.l, c.var, c.stk⟩

def statement (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (statement labels exit next)
  | .peek k f next => .peek k f (statement labels exit next)
  | .pop k f next => .pop k f (statement labels exit next)
  | .load f next => .load f (statement labels exit next)
  | .branch f yes no => .branch f (statement labels exit yes) (statement labels exit no)
  | .goto f => .goto (fun s => labels (f s))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) state tapes =
      configuration labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit a) =
      some (configuration labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) state tapes) = _
          rw [atLabels, stepAux_simulation]

theorem trace (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit a)) = some (configuration labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit a) (some (configuration labels exit b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) run

end BinPackingGames.Foundations.Complexity.MachineSubroutine

namespace BinPackingGames.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def frameStatement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × τ)
  | .push k f next => .push k (fun state => f state.1) (frameStatement next)
  | .peek k f next => .peek k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .pop k f next => .pop k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (frameStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (frameStatement yes) (frameStatement no)
  | .goto f => .goto (fun state => f state.1)
  | .halt => .halt

def frameConfiguration (ambient : τ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × τ) :=
  ⟨c.l, (c.var, ambient), c.stk⟩

def frameProgram (source : Λ → TM2.Stmt Γ Λ σ) : Λ → TM2.Stmt Γ Λ (σ × τ) :=
  fun label => frameStatement (source label)

@[simp] theorem frameConfiguration_state (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.1 = c.var := rfl

@[simp] theorem frameConfiguration_metadata (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.2 = ambient := rfl

@[simp] theorem frameConfiguration_tapes (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).stk = c.stk := rfl

theorem frameStatement_pushBound (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (frameStatement (τ := τ) q) = Runtime.statementPushBound q := by
  induction q <;> simp_all only [frameStatement, Runtime.statementPushBound]

def statement (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' (σ × τ) :=
  MachineSubroutine.statement labels exit (frameStatement q)

def configuration (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' (σ × τ) :=
  MachineSubroutine.configuration labels exit (frameConfiguration ambient c)

@[simp] theorem configuration_state (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.1 = c.var := rfl

@[simp] theorem configuration_metadata (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.2 = ambient := rfl

@[simp] theorem configuration_tapes (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).stk = c.stk := rfl

theorem statement_pushBound (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement (τ := τ) labels exit q) =
      Runtime.statementPushBound q := by
  induction q <;> simp_all only [statement, frameStatement,
    MachineSubroutine.statement, Runtime.statementPushBound]
  cases exit <;> rfl

variable [DecidableEq K]

theorem frame_stepAux (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (frameStatement q) (state, ambient) tapes =
      frameConfiguration ambient (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [frameStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
    | true => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

theorem frame_step (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (frameProgram source) (frameConfiguration ambient c) =
      (TM2.step source c).map (frameConfiguration ambient) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (frameStatement (source label)) (state, ambient) tapes) = _
    rw [frame_stepAux]
    rfl

theorem frame_advance (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    MachineComposition.advance (TM2.step (frameProgram source))
        (c.map (frameConfiguration ambient)) =
      (MachineComposition.advance (TM2.step source) c).map (frameConfiguration ambient) := by
  cases c with
  | none => rfl
  | some c => exact frame_step source ambient c

theorem frame_iterate (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (steps : ℕ) (c : Option (TM2.Cfg Γ Λ σ)) :
    (MachineComposition.advance (TM2.step (frameProgram source)))^[steps]
        (c.map (frameConfiguration ambient)) =
      ((MachineComposition.advance (TM2.step source))^[steps] c).map
        (frameConfiguration ambient) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact frame_advance source ambient _

def frameExecution (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    StateTransition.EvalsToInTime (TM2.step (frameProgram source))
      (frameConfiguration ambient start) (finish.map (frameConfiguration ambient)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (TM2.step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (TM2.step (frameProgram source)))^[run.steps]
      ((some start).map (frameConfiguration ambient)) = finish.map (frameConfiguration ambient)
    rw [frame_iterate, h]
  steps_le_m := run.steps_le_m

@[simp] theorem frameExecution_steps (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    (frameExecution source ambient run).steps = run.steps := rfl

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) (state, ambient) tapes =
      configuration labels exit ambient (TM2.stepAux q state tapes) := by
  rw [statement, MachineSubroutine.stepAux_simulation, frame_stepAux]
  rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit ambient a) =
      some (configuration labels exit ambient b) := by
  have framed : TM2.step (frameProgram source) (frameConfiguration ambient a) =
      some (frameConfiguration ambient b) := by
    rw [frame_step, h]
    rfl
  exact MachineSubroutine.step_simulation labels exit (frameProgram source) target
    atLabels _ _ framed

theorem trace (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : ℕ) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit ambient a)) = some (configuration labels exit ambient b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels)
    steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit ambient a) (some (configuration labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels) run

@[simp] theorem execution_steps (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    (execution labels exit ambient source target atLabels run).steps = run.steps := rfl

end BinPackingGames.Foundations.Complexity.MachineStateFrame

namespace BinPackingGames.Foundations.Complexity.MachineLookup

open Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem select_step_nonempty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) (hinput : input ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter input output⟩ =
      some ⟨some .copy, (ambient, input.head?),
        tapes index source destination base counter input (false :: output)⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  cases input with
  | nil => exact (hinput rfl).elim
  | cons head tail =>
    simp [program, select, Hastad.SourceMachine.fieldStart, TM2.stepAux,
      tapes_source, hsd, update_destination]

theorem select_step_empty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter [] output⟩ =
      some ⟨some .rejected, (ambient, none),
        tapes index source destination base counter [] output⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  simp [program, select, TM2.stepAux, tapes_source, hsd]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

theorem emptyCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) [] output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) [] output⟩ := by
  rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply]
  simp only [Function.iterate_one, advance_some]
  rw [guard_step_succ index source destination his hid]
  exact discard_empty_step source Label.skip Label.guard (program index source destination)
    rfl (tapes index source destination base (encodeWord i ++ indexSuffix) [] output)
    (by simp [hsd]) ambient none

theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

theorem emptyTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[2 * i + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) [] output⟩) =
      some ⟨some .rejected, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) [] output⟩ := by
  induction i generalizing register with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply]
    simp only [Function.iterate_one, advance_some]
    rw [guard_step_zero index source destination his hid]
    exact select_step_empty index source destination hsd base _ output ambient none
  | succ i ih =>
    rw [show 2 * (i + 1) + 2 = (2 * i + 2) + 2 by omega,
      Function.iterate_add_apply, emptyCycleTrace index source destination his hid hsd]
    exact ih none

theorem lookupTrace_invalid (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat) (invalid : values.length ≤ i)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩) =
      some ⟨some .rejected, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) [] output⟩ := by
  induction values generalizing i register with
  | nil =>
    simpa only [MachineLookupSpec.steps, encodeWords] using
      emptyTrace index source destination his hid hsd base i indexSuffix output ambient register
  | cons n values ih =>
    cases i with
    | zero => simp at invalid
    | succ i =>
      simp only [MachineLookupSpec.steps, encodeWords]
      rw [Nat.add_comm (n + 2), Function.iterate_add_apply,
        skipCycleTrace index source destination his hid hsd]
      exact ih i (by simpa using invalid) none

def resultLabel (values : List Nat) (i : Nat) : Label :=
  match values[i]? with
  | some _ => .accepted
  | none => .rejected

def resultOutput (values : List Nat) (i : Nat) (output : List Bool) : List Bool :=
  match values[i]? with
  | some value => encodeWord value ++ output
  | none => output

theorem lookupTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩) =
      some ⟨some (resultLabel values i), (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩ := by
  cases selected : values[i]? with
  | some value =>
    simpa only [List.append_nil, resultLabel, resultOutput, selected] using
      lookupTrace_some index source destination his hid hsd base values i value selected
        indexSuffix [] output ambient register
  | none =>
    have invalid : values.length ≤ i := List.getElem?_eq_none_iff.mp selected
    have hdrop : values.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simpa only [resultLabel, resultOutput, selected, hdrop, encodeWords] using
      lookupTrace_invalid index source destination his hid hsd base values i invalid
        indexSuffix output ambient register

def lookupInTime (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program index source destination))
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩
      (some ⟨some (resultLabel values i), (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩)
      ((encodeWords values).length + 2 * (encodeWord i).length) where
  steps := MachineLookupSpec.steps values i
  evals_in_steps := lookupTrace index source destination his hid hsd base values i
    indexSuffix output ambient register
  steps_le_m := MachineLookupSpec.steps_le_input_encoding_size values i

theorem lookupHaltTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i + 1]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩) =
      some ⟨none, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩ := by
  rw [Function.iterate_succ_apply', lookupTrace index source destination his hid hsd]
  simp only [advance_some]
  cases selected : values[i]? <;> simp [resultLabel, selected, TM2.step, program, TM2.stepAux]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + 1

theorem timePolynomial_bounds (values : List Nat) (i : Nat) :
    MachineLookupSpec.steps values i + 1 ≤
      timePolynomial.eval ((encodeWords values).length + (encodeWord i).length) := by
  have h := MachineLookupSpec.steps_le_input_encoding_size values i
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

def machineInTime (base : Fin 3 → List Bool) (values : List Nat) (i : Nat)
    (indexSuffix output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .guard, ((), register), tapes (K := Fin 3) 0 1 2 base
        (encodeWord i ++ indexSuffix) (encodeWords values) output⟩
      (some ⟨none, ((), none), tapes (K := Fin 3) 0 1 2 base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)))
        (resultOutput values i output)⟩)
      (timePolynomial.eval ((encodeWords values).length + (encodeWord i).length)) where
  steps := MachineLookupSpec.steps values i + 1
  evals_in_steps := lookupHaltTrace (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    base values i indexSuffix output () register
  steps_le_m := timePolynomial_bounds values i

end BinPackingGames.Foundations.Complexity.MachineLookup

namespace BinPackingGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def initialTapes (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord index ++ indexSuffix) workSuffix output

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

def preservingLookupInTime (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient,register), initialTapes tape base i indexSuffix workSuffix output⟩
      (some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩)
      (5 * (encodeWords values).length + 3) where
  steps := 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1
  evals_in_steps := preservingLookupTrace tape distinct firstLabel secondLabel lookupLabels exit
    program atFirst atSecond atLookup base values tableWord scratchEmpty i value selected
    indexSuffix workSuffix output ambient register
  steps_le_m := preservingLookup_steps_le values i value selected

inductive Label
  | copyFirst | copySecond | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .copyFirst
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program id

end BinPackingGames.Foundations.Complexity.MachinePreservingLookup

namespace BinPackingGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | run (label : MachinePreservingLookup.Label)
  | cleanup
  deriving DecidableEq, Fintype

def statement (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .run label => MachineSubroutine.statement (fun label => labels (.run label))
      (some (labels .cleanup)) (MachinePreservingLookup.program tape label)
  | .cleanup => MachineDrain.drain (tape 2) (labels .cleanup) exit

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool) :=
  statement tape id none

def steps (values : List Nat) (index : Nat) : Nat :=
  (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) +
    ((encodeWords (values.drop (index + 1))).length + 1)

theorem remaining_length_le (values : List Nat) (index : Nat) :
    (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop (index + 1) values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem steps_le (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ 6 * (encodeWords values).length + 4 := by
  have hc := MachinePreservingLookup.preservingLookup_steps_le values index value selected
  have hd := remaining_length_le values index
  unfold steps
  omega

noncomputable def timePolynomial : Polynomial Nat := 6 * Polynomial.X + 4

theorem steps_le_timePolynomial (values : List Nat) (index value : Nat)
    (selected : values[index]? = some value) :
    steps values index ≤ timePolynomial.eval (encodeWords values).length := by
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X] using steps_le values index value selected

theorem traceAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b :=
    fun h => hne (distinct h)
  have raw := MachinePreservingLookup.preservingLookupTrace tape distinct
    MachinePreservingLookup.Label.copyFirst MachinePreservingLookup.Label.copySecond
    MachinePreservingLookup.Label.lookup none (MachinePreservingLookup.program tape)
    rfl rfl (fun _ => rfl) base values tableWord scratchEmpty index value selected
    indexSuffix [] output ambient register
  have run := MachineSubroutine.trace (fun label => labels (.run label))
    (some (labels .cleanup)) (MachinePreservingLookup.program tape) target
    (fun label => code (.run label))
    (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1)
    _ _ raw
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at run
  have cleanup := MachineDrain.drainTrace (tape 2) (labels .cleanup) exit target
    (code .cleanup)
    (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
    (encodeWords (values.drop (index + 1))) ambient none
  have word : MachinePreservingLookup.finalTapes tape base values index value
      indexSuffix [] output (tape 2) = encodeWords (values.drop (index + 1)) := by
    simp only [MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.append_nil]
  have start : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) (encodeWords (values.drop (index + 1))) =
      MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output := by
    rw [← word, Function.update_eq_self]
  have finish : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) [] = MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
        (encodeWord value ++ output) := by
    unfold MachinePreservingLookup.finalTapes MachinePreservingLookup.initialTapes
    rw [MachineLookup.update_source _ _ _ (hd 2 3 (by decide))]
  rw [start, finish] at cleanup
  rw [show steps values index =
      ((encodeWords (values.drop (index + 1))).length + 1) +
        (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) by
        unfold steps
        omega,
    Function.iterate_add_apply, run]
  exact cleanup

def inTimeAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩
      (some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩)
      (timePolynomial.eval (encodeWords values).length) where
  steps := steps values index
  evals_in_steps := traceAt tape distinct labels exit target code base values tableWord
    scratchEmpty index value selected indexSuffix output ambient register
  steps_le_m := steps_le_timePolynomial values index value selected

theorem initialTapes_eq (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) :
    MachinePreservingLookup.initialTapes tape base index indexSuffix [] (base (tape 3)) =
      base := by
  simp only [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
    ← counterWord, ← workEmpty, Function.update_eq_self]

theorem traceAt_fromTapes (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ base (tape 3))⟩ := by
  have h := traceAt tape distinct labels exit target code base values tableWord scratchEmpty
    index value selected indexSuffix (base (tape 3)) ambient register
  rw [initialTapes_eq tape base index indexSuffix counterWord workEmpty] at h
  exact h

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := .run .copyFirst
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program id

def machineInTime (base : Fin 5 → List Bool) (values : List Nat)
    (tableWord : base 0 = encodeWords values) (scratchEmpty : base 4 = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨some (.run .copyFirst), ((), register),
        MachinePreservingLookup.initialTapes id base index indexSuffix [] output⟩
      (some ⟨none, ((), none),
        MachinePreservingLookup.initialTapes id base 0 indexSuffix []
          (encodeWord value ++ output)⟩)
      (timePolynomial.eval (encodeWords values).length) :=
  inTimeAt id (fun _ _ h => h) id none (program id) (fun _ => rfl)
    base values tableWord scratchEmpty index value selected indexSuffix output () register

end BinPackingGames.Foundations.Complexity.MachinePreservingLookupClean

namespace BinPackingGames.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.inputVertex, .table, .output, .emitScratch,
  .queryReverse, .queryIndex, .lookupOutput, .lookupWork, .lookupRestore, .quotientFirst,
  .quotientSecond, .remainderFirst, .remainderSecond]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label (d : Nat)
  | initialize
  | firstEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | firstReverse
  | firstLookup (label : MachinePreservingLookupClean.Label)
  | firstScan
  | firstResidue (r : Fin (degree d))
  | clearQuery
  | secondEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | secondReverse
  | secondLookup (label : MachinePreservingLookupClean.Label)
  | secondScan
  | secondResidue (r : Fin (degree d))
  | outputEmit (label : PCP.AlphabetTable.Emitter.Label 3 (rowFactor d))
  | cleanup (i : Fin 6)
  | done
  deriving DecidableEq, Fintype

abbrev Ambient (ρ : Type) (d : Nat) := ρ × Control d
abbrev State (ρ : Type) (d : Nat) :=
  PCP.AlphabetTable.Emitter.State (Ambient ρ d × Fin (degree d))

def divisionStates (ρ : Type) (d : Nat) :
    MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.1.2), ()), s.2)
  invFun s := (((s.1.1.1, ()), s.1.1.2), s.2)
  left_inv := by rintro ⟨⟨⟨a, u⟩, r⟩, b⟩; cases u; rfl
  right_inv := by rintro ⟨⟨⟨a, r⟩, u⟩, b⟩; cases u; rfl

def firstFinish {ρ : Type} {d : Nat} (s : Ambient ρ d × Unit)
    (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveFirst s.1.2 r), ())

def secondFinish {ρ : Type} {d : Nat} (H : Table (cloudSize d) d)
    (s : Ambient ρ d × Unit) (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveSecond H s.1.2 r), ())

def affinePlan {σ : Type} {bound : Nat} (coefficient : Nat) (offset : σ → Fin bound) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 σ bound :=
  PCP.AlphabetTable.Emitter.listCommands
    (PCP.AlphabetTable.Emitter.affineCommands [(0, coefficient)] offset)

def firstPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => firstOffset s.1.2)

def secondPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => secondOffset s.1.2)

def outputPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (rowFactor d) :=
  affinePlan (rowFactor d) (fun s => outputOffset s.1.2)

def lookupTape : Fin 5 → Tape
  | ⟨0, _⟩ => .table
  | ⟨1, _⟩ => .queryIndex
  | ⟨2, _⟩ => .lookupWork
  | ⟨3, _⟩ => .lookupOutput
  | _ => .lookupRestore

def dirtyTape : Fin 6 → Tape
  | ⟨0, _⟩ => .queryIndex
  | ⟨1, _⟩ => .lookupOutput
  | ⟨2, _⟩ => .quotientFirst
  | ⟨3, _⟩ => .quotientSecond
  | ⟨4, _⟩ => .remainderFirst
  | _ => .remainderSecond

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

def statement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d)
  | .initialize =>
    .push (ports .quotientFirst) (fun _ => false)
      (.push (ports .quotientSecond) (fun _ => false)
        (.push (ports .remainderFirst) (fun _ => false)
          (.push (ports .remainderSecond) (fun _ => false)
            (.load (fun s => (s.1, none))
              (.goto fun _ => labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry)))))))
  | .firstEmit l =>
    PCP.AlphabetTable.Emitter.statement (firstPlan ρ d) (fun _ => ports .inputVertex)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
      (some (labels .firstReverse)) l
  | .firstReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .firstReverse)
      (some (labels (.firstLookup (.run .copyFirst))))
  | .firstLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.firstLookup k)) (some (labels .firstScan)) l
  | .firstScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r)))
  | .firstResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r)
  | .clearQuery =>
    .pop (ports .queryIndex) (fun s _ => s)
      (.pop (ports .lookupOutput) (fun s _ => s)
        (.goto fun _ => labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
  | .secondEmit l =>
    PCP.AlphabetTable.Emitter.statement (secondPlan ρ d) (fun _ => ports .quotientFirst)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
      (some (labels .secondReverse)) l
  | .secondReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .secondReverse)
      (some (labels (.secondLookup (.run .copyFirst))))
  | .secondLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.secondLookup k)) (some (labels .secondScan)) l
  | .secondScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r)))
  | .secondResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderSecond)
        (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
        (secondFinish H) r)
  | .outputEmit l =>
    PCP.AlphabetTable.Emitter.statement (outputPlan ρ d) (fun _ => ports .quotientSecond)
      (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
      (some (labels (.cleanup 0))) l
  | .cleanup i =>
    MachineDrain.drain (ports (dirtyTape i)) (labels (.cleanup i))
      (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩) else labels .done))
  | .done => Reduction.MachineTransfer.exitAt (ports .output) exit

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State ρ d) :=
  statement positive H id id none

end

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

private theorem controlStatement_inverse {K Λ σ τ : Type} {Γ : K → Type}
    (e : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id e.symm (MachineControl.statement id e q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

private theorem transportedDivision {K Λ σ τ : Type} [DecidableEq K] [Fintype σ]
    (q : Nat) (positive : 0 < q) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder)
    (states : MachineFixedDivMod.State σ q ≃ τ)
    (scanLabel : Λ) (emitterLabel : Fin q → Λ) (exit : Option Λ)
    (finish : σ → Fin q → σ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (atScan : target scanLabel = MachineControl.statement id states
      (MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel))
    (atEmitter : ∀ r, target (emitterLabel r) = MachineControl.statement id states
      (MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r))
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some (MachineControl.configuration id states
        ⟨some scanLabel, ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩)) =
      some (MachineControl.configuration id states
        ⟨exit, ((finish ambient (MachineFixedDivMod.residue q positive n),
          MachineFixedDivMod.residue q positive 0), none),
          MachineFixedDivMod.unaryTapes source quotient remainder base 0 (n / q) (n % q)
            sourceSuffix quotientSuffix remainderSuffix⟩) := by
  let sourceProgram := MachineControl.program (Equiv.refl Λ) states.symm target
  have sourceScan : sourceProgram scanLabel =
      MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel := by
    change MachineControl.statement id states.symm (target scanLabel) = _
    rw [atScan]
    exact controlStatement_inverse states _
  have sourceEmit : ∀ r, sourceProgram (emitterLabel r) =
      MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r := by
    intro r
    change MachineControl.statement id states.symm (target (emitterLabel r)) = _
    rw [atEmitter]
    exact controlStatement_inverse states _
  have htrace := MachineFixedDivMod.divModFromTapesWithFinish q positive source quotient
    remainder sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel exit
    finish sourceProgram sourceScan sourceEmit base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ambient register
  have roundtrip : MachineControl.program (Equiv.refl Λ) states sourceProgram = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatement_inverse states.symm _
  have simulation : ∀ a b, TM2.step sourceProgram a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states sourceProgram a
    rw [roundtrip, hab] at h
    exact h
  exact MachineComposition.liftSuccessfulTrace (TM2.step sourceProgram) (TM2.step target)
    (MachineControl.configuration id states) simulation (n + 2) _ _ htrace

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

@[simp] theorem divisionStates_apply (ρ : Type) (d : Nat)
    (s : MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d)) :
    divisionStates ρ d s = (((s.1.1.1, s.1.2), ()), s.2) := rfl

def divisionState {d : Nat} (positive : 0 < d) (ambient : ρ) (control : Control d)
    (register : Option Bool) : State ρ d :=
  ((((ambient, control),
    MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0), ()), register)

def divisionOutput (d : Nat) (ports : Tape → K) (quotient remainder : Tape)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (ports .lookupOutput) (ports quotient) (ports remainder)
    base 0 (n / degree d) (n % degree d) sourceSuffix quotientSuffix remainderSuffix

theorem firstDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientFirst) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderFirst) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient
        (receiveFirst control (MachineFixedDivMod.residue (degree d)
          (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientFirst .remainderFirst base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientFirst ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .firstScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r))) := atProgram .firstScan
  have he : ∀ r, target (labels (.firstResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r) :=
    fun r => atProgram (.firstResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientFirst) (ports .remainderFirst) hsq hsr hqr
    (divisionStates ρ d) (labels .firstScan) (fun r => labels (.firstResidue r))
    (some (labels .clearQuery)) firstFinish target hs he base n sourceSuffix quotientSuffix
    remainderSuffix sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, firstFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

theorem secondDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientSecond) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderSecond) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient
          (receiveSecond H control (MachineFixedDivMod.residue (degree d)
            (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientSecond .remainderSecond base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientSecond ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .secondScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r))) := atProgram .secondScan
  have he : ∀ r, target (labels (.secondResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderSecond)
          (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
          (secondFinish H) r) := fun r => atProgram (.secondResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientSecond) (ports .remainderSecond) hsq hsr hqr
    (divisionStates ρ d) (labels .secondScan) (fun r => labels (.secondResidue r))
    (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
    (secondFinish H) target hs he base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, secondFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

@[simp] theorem divisionOutput_source (d : Nat) (ports : Tape → K)
    (portsInjective : Function.Injective ports) (quotient remainder : Tape)
    (notSourceQuotient : Tape.lookupOutput ≠ quotient)
    (notSourceRemainder : Tape.lookupOutput ≠ remainder)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports .lookupOutput) = encodeWord 0 ++ sourceSuffix := by
  exact MachineFixedDivMod.unaryTapes_source _ _ _
    (fun h => notSourceQuotient (portsInjective h))
    (fun h => notSourceRemainder (portsInjective h)) _ _ _ _ _ _ _

@[simp] theorem divisionOutput_quotient (d : Nat) (ports : Tape → K)
    (portsInjective : Function.Injective ports) (quotient remainder : Tape)
    (distinct : quotient ≠ remainder) (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports quotient) = encodeWord (n / degree d) ++ quotientSuffix := by
  exact MachineFixedDivMod.unaryTapes_quotient _ _ _
    (fun h => distinct (portsInjective h)) _ _ _ _ _ _ _

@[simp] theorem divisionOutput_remainder (d : Nat) (ports : Tape → K)
    (quotient remainder : Tape) (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports remainder) = encodeWord (n % degree d) ++ remainderSuffix := by
  exact MachineFixedDivMod.unaryTapes_remainder _ _ _ _ _ _ _ _ _ _

theorem divisionOutput_other (d : Nat) (ports : Tape → K) (quotient remainder : Tape)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) (other : K)
    (notSource : other ≠ ports .lookupOutput) (notQuotient : other ≠ ports quotient)
    (notRemainder : other ≠ ports remainder) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      other = base other := by
  exact MachineFixedDivMod.unaryTapes_other _ _ _ other notSource notQuotient notRemainder
    _ _ _ _ _ _ _

def firstDivisionInTime {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientFirst) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderFirst) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .firstScan), divisionState positive ambient control register, base⟩
      (some ⟨some (labels .clearQuery), divisionState positive ambient
        (receiveFirst control (MachineFixedDivMod.residue (degree d)
          (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientFirst .remainderFirst base n
          sourceSuffix quotientSuffix remainderSuffix⟩) (n + 2) where
  steps := n + 2
  evals_in_steps := firstDivisionTrace positive H ports portsInjective labels exit target atProgram
    base n sourceSuffix quotientSuffix remainderSuffix sourceInput quotientInput remainderInput
    ambient control register
  steps_le_m := Nat.le_refl _

def secondDivisionInTime {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientSecond) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderSecond) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .secondScan), divisionState positive ambient control register, base⟩
      (some ⟨some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient
          (receiveSecond H control (MachineFixedDivMod.residue (degree d)
            (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientSecond .remainderSecond base n
          sourceSuffix quotientSuffix remainderSuffix⟩) (n + 2) where
  steps := n + 2
  evals_in_steps := secondDivisionTrace positive H ports portsInjective labels exit target atProgram
    base n sourceSuffix quotientSuffix remainderSuffix sourceInput quotientInput remainderInput
    ambient control register
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.MachineExpanderRow

end OAI
