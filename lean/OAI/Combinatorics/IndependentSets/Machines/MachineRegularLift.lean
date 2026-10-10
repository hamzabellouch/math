import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineStateEquiv
import OAI.Combinatorics.IndependentSets.Machines.MachineCloudPadding
import OAI.Combinatorics.IndependentSets.Machines.MachineStateFrame

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

namespace Lift

open MachineCloudPadding

variable {K K' Λ Λ' σ τ υ : Type}

def statement (tape : K → K') (labels : Λ → Λ') (exit : Option Λ')
    (registers : (σ × τ) ≃ υ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2.Stmt (fun _ : K' => Bool) Λ' υ :=
  MachineStateEquiv.statement registers
    (MachineStateFrame.frameStatement (Placement.statement tape labels exit q))

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (registers : (σ × τ) ≃ υ) (ambient : τ) (extra : K' → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) : TM2.Cfg (fun _ : K' => Bool) Λ' υ :=
  ⟨Placement.label labels exit c.l, registers (c.var, ambient),
    Placement.tapes view c.stk extra⟩

variable [DecidableEq K] [DecidableEq K']

theorem stepAux (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit registers q) (registers (state, ambient))
        (Placement.tapes view source extra) =
      configuration view labels exit registers ambient extra (TM2.stepAux q state source) := by
  rw [statement, MachineStateEquiv.stepAux_transport, MachineStateFrame.frame_stepAux,
    Placement.stepAux_simulation tape view left right]
  rfl

theorem step (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit registers ambient extra a) =
      some (configuration view labels exit registers ambient extra b) := by
  cases a with
  | mk label state sourceTapes =>
    cases label with
    | none => simp [TM2.step] at h
    | some label =>
      have hb : TM2.stepAux (source label) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels label)) (registers (state, ambient))
        (Placement.tapes view sourceTapes extra)) = _
      rw [code, stepAux tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (registers : (σ × τ) ≃ υ)
    (ambient : τ) (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' υ)
    (code : ∀ l, target (labels l) = statement tape labels exit registers (source l))
    (steps : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[steps] (some a) = some b) :
    (advance (TM2.step target))^[steps]
      (some (configuration view labels exit registers ambient extra a)) =
      some (configuration view labels exit registers ambient extra b) :=
  liftSuccessfulTrace _ _ _
    (step tape view left right labels exit registers ambient extra source target code) steps a b run

end Lift

end IndependentSetsGames.Foundations.Complexity.MachineRegularTable

end OAI
