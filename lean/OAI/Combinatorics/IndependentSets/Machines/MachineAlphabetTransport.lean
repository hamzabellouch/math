import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineComposition

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

def tapes (h : Γ = Δ) (source : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ source

def statement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := h ▸ source

def configuration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := h ▸ source

def program (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ :=
  fun label => statement h (source label)

abbrev castStatement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := statement h source
abbrev castConfiguration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := configuration h source
abbrev castProgram (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ := program h source

@[simp] theorem tapes_rfl (source : ∀ k, List (Γ k)) : tapes rfl source = source := rfl
@[simp] theorem statement_rfl (source : Stmt Γ Λ σ) : statement rfl source = source := rfl
@[simp] theorem configuration_rfl (source : Cfg Γ Λ σ) : configuration rfl source = source := rfl
@[simp] theorem program_rfl (source : Λ → Stmt Γ Λ σ) : program rfl source = source := rfl

@[simp] theorem program_apply (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (label : Λ) :
    program h source label = statement h (source label) := rfl

@[simp] theorem statement_roundtrip (h : Γ = Δ) (source : Stmt Δ Λ σ) :
    statement h (statement h.symm source) = source := by cases h; rfl

@[simp] theorem statement_symm_roundtrip (h : Γ = Δ) (source : Stmt Γ Λ σ) :
    statement h.symm (statement h source) = source := by cases h; rfl

@[simp] theorem configuration_roundtrip (h : Γ = Δ) (source : Cfg Δ Λ σ) :
    configuration h (configuration h.symm source) = source := by cases h; rfl

@[simp] theorem configuration_symm_roundtrip (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    configuration h.symm (configuration h source) = source := by cases h; rfl

@[simp] theorem program_roundtrip (h : Γ = Δ) (source : Λ → Stmt Δ Λ σ) :
    program h (program h.symm source) = source := by cases h; rfl

@[simp] theorem program_symm_roundtrip (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) :
    program h.symm (program h source) = source := by cases h; rfl

@[simp] theorem tapes_roundtrip (h : Γ = Δ) (source : ∀ k, List (Δ k)) :
    tapes h (tapes h.symm source) = source := by cases h; rfl

@[simp] theorem tapes_symm_roundtrip (h : Γ = Δ) (source : ∀ k, List (Γ k)) :
    tapes h.symm (tapes h source) = source := by cases h; rfl

@[simp] theorem configuration_label (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).l = source.l := by cases h; rfl

@[simp] theorem configuration_state (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).var = source.var := by cases h; rfl

@[simp] theorem configuration_tapes (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).stk = tapes h source.stk := by cases h; rfl

@[simp] theorem configuration_mk (h : Γ = Δ) (label : Option Λ) (state : σ)
    (source : ∀ k, List (Γ k)) :
    configuration h ⟨label, state, source⟩ = ⟨label, state, tapes h source⟩ := by cases h; rfl

@[simp] theorem map_configuration_rfl (source : Option (Cfg Γ Λ σ)) :
    source.map (configuration (rfl : Γ = Γ)) = source := by cases source <;> rfl

variable [DecidableEq K]

theorem stepAux_simulation (h : Γ = Δ) (source : Stmt Γ Λ σ) (state : σ)
    (sourceTapes : ∀ k, List (Γ k)) :
    stepAux (statement h source) state (tapes h sourceTapes) =
      configuration h (stepAux source state sourceTapes) := by cases h; rfl

theorem step_simulation (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (start : Cfg Γ Λ σ) :
    step (program h source) (configuration h start) =
      (step source start).map (configuration h) := by
  cases h
  simp only [program_rfl, configuration_rfl, map_configuration_rfl]

theorem trace_transport (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program h source)))^[n]
      (start.map (configuration h)) =
      ((MachineComposition.advance (step source))^[n] start).map (configuration h) := by
  cases h
  simp only [program_rfl, map_configuration_rfl]

theorem successfulTrace (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start finish : Cfg Γ Λ σ)
    (trace : (MachineComposition.advance (step source))^[n] (some start) = some finish) :
    (MachineComposition.advance (step (program h source)))^[n]
      (some (configuration h start)) = some (configuration h finish) := by
  have transported := trace_transport h source n (some start)
  simpa only [Option.map_some, trace] using transported

def executionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (finish.map (configuration h)) budget where
  steps := execution.steps
  evals_in_steps := by
    cases h
    simpa only [program_rfl, configuration_rfl, map_configuration_rfl]
      using execution.evals_in_steps
  steps_le_m := execution.steps_le_m

@[simp] theorem executionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    (executionInTime h source execution).steps = execution.steps := rfl

def successfulExecutionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (some (configuration h finish)) budget := executionInTime h source execution

@[simp] theorem successfulExecutionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    (successfulExecutionInTime h source execution).steps = execution.steps := rfl

end IndependentSetsGames.Foundations.Complexity.MachineAlphabetTransport

end OAI
