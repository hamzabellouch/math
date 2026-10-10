import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineFiniteAlphabet
import OAI.Combinatorics.IndependentSets.Machines.MachineRegularTableBounds

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineCanonicalOutput
open Turing MachineComposition
section Structural

variable {K Λ Λ' σ : Type} [DecidableEq K]

def extendedLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def extendedCfg (labels : Λ → Λ') (haltTarget : Option Λ') (register : Option Bool)
    (cfg : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ' (σ × Option Bool) :=
  ⟨extendedLabel labels haltTarget cfg.l, (cfg.var, register), cfg.stk⟩

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
      exact congrArg some (stepAux_extended Sum.inl (cleanupEntry chosen)
        (P.code label) state none tapes)

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
      exact congrArg some ((congrArg (fun tapes =>
        (⟨none, (P.initial, none), tapes⟩ : (completedMachine P chosen).Cfg))
          (finalTapes_eq P chosen complete base)).trans
            (haltList_eq P chosen (base P.output)).symm)
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

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

structure TerminalRun (P : Program K Λ σ) (input output : List Bool) (budget : Nat) where
  state : σ
  tapes : K → List Bool
  execution : StateTransition.EvalsToInTime (sourceMachine P).step
    (initList (sourceMachine P) input) (some ⟨none, state, tapes⟩) budget
  output_eq : tapes P.output = output

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
    dsimp only [completedMachine]
    rw [List.map_id, List.map_id, completedTime_eval]
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

end IndependentSetsGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
