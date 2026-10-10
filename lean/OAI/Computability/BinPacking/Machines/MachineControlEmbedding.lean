import OAI.Computability.BinPacking.Computation.MachineExpanderRowDivision

namespace OAI

namespace BinPackingGap.MachineControlEmbedding

open Turing
open BinPackingGames.Foundations.Complexity

structure Control (σ τ : Type) where
  put : σ → τ
  get : τ → σ
  get_put : ∀ s, get (put s) = s

namespace Control

def left {σ τ : Type} (fallback : σ) : Control σ (σ ⊕ τ) where
  put := Sum.inl
  get := Sum.elim id (fun _ => fallback)
  get_put _ := rfl

def right {σ τ : Type} (fallback : τ) : Control τ (σ ⊕ τ) where
  put := Sum.inr
  get := Sum.elim (fun _ => fallback) id
  get_put _ := rfl

def trans {σ τ υ : Type} (e : Control σ τ) (f : Control τ υ) : Control σ υ where
  put := f.put ∘ e.put
  get := e.get ∘ f.get
  get_put s := by simp only [Function.comp_apply, f.get_put, e.get_put]

end Control

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def statement (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' τ
  | .push k f next => .push k (fun s => f (control.get s))
      (statement control labels exit next)
  | .peek k f next => .peek k (fun s bit => control.put (f (control.get s) bit))
      (statement control labels exit next)
  | .pop k f next => .pop k (fun s bit => control.put (f (control.get s) bit))
      (statement control labels exit next)
  | .load f next => .load (fun s => control.put (f (control.get s)))
      (statement control labels exit next)
  | .branch f yes no => .branch (fun s => f (control.get s))
      (statement control labels exit yes) (statement control labels exit no)
  | .goto f => .goto (fun s => labels (f (control.get s)))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

def configuration (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ')
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' τ :=
  ⟨MachineSubroutine.label labels exit c.l, control.put c.var, c.stk⟩

theorem statement_pushBound (control : Control σ τ) (labels : Λ → Λ')
    (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (statement control labels exit q) =
      Runtime.statementPushBound q := by
  induction q <;> simp_all only [statement, Runtime.statementPushBound]
  cases exit <;> rfl

variable [DecidableEq K]

theorem stepAux_simulation (control : Control σ τ) (labels : Λ → Λ')
    (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement control labels exit q) (control.put state) tapes =
      configuration control labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using
        ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false =>
          simpa only [statement, TM2.stepAux, control.get_put, h, Bool.cond_false]
            using ihNo state tapes
      | true =>
          simpa only [statement, TM2.stepAux, control.get_put, h, Bool.cond_true]
            using ihYes state tapes
  | goto f => simp only [statement, TM2.stepAux, control.get_put, configuration,
      MachineSubroutine.label]
  | halt => cases exit <;> rfl

theorem step_simulation (control : Control σ τ) (labels : Λ → Λ')
    (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' τ)
    (atLabels : ∀ l, target (labels l) = statement control labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration control labels exit a) =
      some (configuration control labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) (control.put state) tapes) = _
          rw [atLabels, stepAux_simulation]

theorem trace (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' τ)
    (atLabels : ∀ l, target (labels l) = statement control labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration control labels exit a)) =
      some (configuration control labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration control labels exit)
    (step_simulation control labels exit source target atLabels) steps a b run

def execution (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' τ)
    (atLabels : ∀ l, target (labels l) = statement control labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration control labels exit a)
      (some (configuration control labels exit b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration control labels exit)
    (step_simulation control labels exit source target atLabels) run

end BinPackingGap.MachineControlEmbedding

end OAI
