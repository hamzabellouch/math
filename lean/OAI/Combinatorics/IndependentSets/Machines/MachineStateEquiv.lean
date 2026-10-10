import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineBudget
import OAI.Combinatorics.IndependentSets.Machines.MachineControl

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

abbrev statement (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ :=
  MachineControl.statement (id : Λ → Λ) e

@[simp] theorem statement_symm_statement (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    statement e.symm (statement e q) = q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Equiv.symm_symm,
      Equiv.symm_apply_apply, id_eq]

def configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

@[simp] theorem configuration_label (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).l = c.l := rfl

@[simp] theorem configuration_state (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).var = e c.var := rfl

@[simp] theorem configuration_tapes (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).stk = c.stk := rfl

@[simp] theorem configuration_symm_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configuration e.symm (configuration e c) = c := by
  cases c
  simp only [configuration, Equiv.symm_apply_apply]

@[simp] theorem configuration_configuration_symm (e : σ ≃ τ) (c : Cfg Γ Λ τ) :
    configuration e (configuration e.symm c) = c := by
  cases c
  simp only [configuration, Equiv.apply_symm_apply]

def configurationEquiv (e : σ ≃ τ) : Cfg Γ Λ σ ≃ Cfg Γ Λ τ where
  toFun := configuration e
  invFun := configuration e.symm
  left_inv := configuration_symm_configuration e
  right_inv := configuration_configuration_symm e

@[simp] theorem configurationEquiv_apply (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configurationEquiv e c = configuration e c := rfl

@[simp] theorem control_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    MachineControl.configuration (id : Λ → Λ) e c = configuration e c := by
  cases c
  simp [MachineControl.configuration, configuration]

def program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Γ Λ τ :=
  fun l => statement e (source l)

@[simp] theorem program_symm_program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) :
    program e.symm (program e source) = source := by
  funext l
  exact statement_symm_statement e (source l)

theorem statementPushBound (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement e q) = Runtime.statementPushBound q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Runtime.statementPushBound]

theorem supportsStmt_iff (e : σ ≃ τ) (S : Finset Λ) (q : Stmt Γ Λ σ) :
    SupportsStmt S (statement e q) ↔ SupportsStmt S q := by
  induction q with
  | push k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | peek k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | pop k f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | load f next ih =>
      simpa only [statement, MachineControl.statement, SupportsStmt] using ih
  | branch f yes no ihYes ihNo =>
      simp only [statement, MachineControl.statement, SupportsStmt, ihYes, ihNo]
  | goto f =>
      change (∀ state : τ, f (e.symm state) ∈ S) ↔ ∀ state : σ, f state ∈ S
      constructor
      · intro h state
        simpa only [Equiv.symm_apply_apply] using h (e state)
      · intro h state
        exact h (e.symm state)
  | halt => rfl

theorem supports_iff [Inhabited Λ] (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (S : Finset Λ) : Supports (program e source) S ↔ Supports source S := by
  simp only [Supports, program, supportsStmt_iff]

variable [DecidableEq K]

theorem stepAux_transport (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) (e state) tapes =
      configuration e (stepAux q state tapes) := by
  simpa only [statement, control_configuration] using
    MachineControl.stepAux_simulation (id : Λ → Λ) e q state tapes

theorem stepAux_transport_symm (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : τ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) state tapes =
      configuration e (stepAux q (e.symm state) tapes) := by
  simpa only [Equiv.apply_symm_apply] using
    stepAux_transport e q (e.symm state) tapes

theorem step_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program e source) (configuration e c) =
      (step source c).map (configuration e) := by
  cases c with
  | mk l state tapes =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (statement e (source l)) (e state) tapes) = _
          rw [stepAux_transport]
          rfl

theorem step_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (a b : Cfg Γ Λ σ) :
    step (program e source) (configuration e a) = some (configuration e b) ↔
      step source a = some b := by
  rw [step_transport]
  change (step source a).map (configuration e) = (some b).map (configuration e) ↔ _
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change (step source a).map (configuration e) = (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem advance_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (c : Option (Cfg Γ Λ σ)) :
    MachineComposition.advance (step (program e source)) (c.map (configuration e)) =
      (MachineComposition.advance (step source) c).map (configuration e) := by
  cases c with
  | none => rfl
  | some c => exact step_transport e source c

theorem iterate_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program e source)))^[n]
        (c.map (configuration e)) =
      ((MachineComposition.advance (step source))^[n] c).map (configuration e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

theorem trace_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ) :
    (MachineComposition.advance (step (program e source)))^[n]
        (some (configuration e a)) = some (configuration e b) ↔
      (MachineComposition.advance (step source))^[n] (some a) = some b := by
  change (MachineComposition.advance (step (program e source)))^[n]
      ((some a).map (configuration e)) = (some b).map (configuration e) ↔ _
  rw [iterate_transport]
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[n] (some a)).map (configuration e) =
      (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem trace (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ)
    (run : (MachineComposition.advance (step source))^[n] (some a) = some b) :
    (MachineComposition.advance (step (program e source)))^[n]
      (some (configuration e a)) = some (configuration e b) :=
  (trace_iff e source n a b).2 run

def execution (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (step (program e source)))^[run.steps]
      ((some start).map (configuration e)) = finish.map (configuration e)
    rw [iterate_transport, h]
  steps_le_m := run.steps_le_m

@[simp] theorem execution_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    (execution e source run).steps = run.steps := rfl

def execution_reflect (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    StateTransition.EvalsToInTime (step source) start finish budget where
  steps := run.steps
  evals_in_steps := by
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[run.steps] (some start)).map
      (configuration e) = finish.map (configuration e)
    rw [← iterate_transport]
    exact run.evals_in_steps
  steps_le_m := run.steps_le_m

@[simp] theorem execution_reflect_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    (execution_reflect e source run).steps = run.steps := rfl

end IndependentSetsGames.Foundations.Complexity.MachineStateEquiv

end OAI
