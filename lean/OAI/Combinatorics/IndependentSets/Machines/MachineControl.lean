import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.GenericGraphTables
import OAI.Combinatorics.IndependentSets.Machines.MachineCompare

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

def program (labels : Λ ≃ Λ') (states : σ ≃ σ') (source : Λ → Stmt Γ Λ σ) :
    Λ' → Stmt Γ Λ' σ' := fun l => statement labels states (source (labels.symm l))

theorem step_simulation (labels : Λ ≃ Λ') (states : σ ≃ σ')
    (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program labels states source) (configuration labels states c) =
      (step source c).map (configuration labels states) := by
  cases c with
  | mk l state tapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement labels states (source (labels.symm (labels l))))
        (states state) tapes) = _
      rw [Equiv.symm_apply_apply, stepAux_simulation]
      rfl

end IndependentSetsGames.Foundations.Complexity.MachineControl
namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open IndependentSetsGames.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

instance : Fintype Tape where
  elems := {.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan,
    .compareLeft, .compareRight, .reversed, .output}
  complete tape := by cases tape <;> simp

abbrev Alphabet (_ : Tape) := Bool

abbrev Flags := Bool × Bool × Option Bool
abbrev Ambient (q : Nat) := Flags × GenericGraphTables.RelationTable q
abbrev State (q : Nat) := Ambient q × Option Bool

def normal {q : Nat} (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) : State q :=
  (((selfLoop, false, none), relation), none)

def initial (q : Nat) : State q := normal (Vector.replicate (q * q) false) false

def context {q : Nat} (ambient : Ambient q) : GenericGraphTables.RelationTable q × Bool :=
  (ambient.2, ambient.1.1)

def compareEquiv (q : Nat) : State q ≃
    MachineCompare.State (GenericGraphTables.RelationTable q × Bool) where
  toFun s := ((s.1.2, s.1.1.1), s.1.1.2.1, s.1.1.2.2, s.2)
  invFun s := (((s.1.2, s.2.1, s.2.2.1), s.1.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem compareEquiv_normal {q : Nat}
    (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) :
    compareEquiv q (normal relation selfLoop) =
      ((relation, selfLoop), false, none, none) := rfl

def emitterEquiv (q : Nat) : ((Ambient q × Unit) × Option Bool) ≃ State q where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv s := by rcases s with ⟨⟨s, u⟩, r⟩; cases u; rfl
  right_inv _ := rfl

def setupPorts : Fin 7 → Tape :=
  ![.original, .cursor, .vertices, .darts, .counter, .scratch, .edge]

theorem setupPorts_injective : Function.Injective setupPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [setupPorts]

def headPorts : Fin 6 → Tape :=
  ![.original, .reverseIndex, .scan, .indexScan, .head, .scratch]

theorem headPorts_injective : Function.Injective headPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headPorts]

def rowSources : Fin 5 → Tape := ![.vertices, .darts, .edge, .tail, .head]
def headerSources : Fin 2 → Tape := ![.vertices, .darts]
def fieldPorts : Fin 3 → Tape := ![.tail, .reverseIndex, .head]

def cleanupPorts : Fin 15 → Tape :=
  ![.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight, .reversed]

theorem cleanupPorts_ne_output (i : Fin 15) : cleanupPorts i ≠ .output := by
  fin_cases i <;> simp [cleanupPorts]

theorem cleanupPorts_cover (tape : Tape) (h : tape ≠ .output) :
    ∃ i, cleanupPorts i = tape := by
  cases tape
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact (h rfl).elim

variable {Λ : Type} {q : Nat}

def compareStatement (stmt : TM2.Stmt Alphabet Λ
    (MachineCompare.State (GenericGraphTables.RelationTable q × Bool))) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (compareEquiv q).symm stmt

def emitterStatement (stmt : TM2.Stmt Alphabet Λ ((Ambient q × Unit) × Option Bool)) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (emitterEquiv q) stmt

def storeLoop (value : Bool) (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .load (fun state => (((value, false, none), state.1.2), none)) (.goto fun _ => next)

theorem stepAux_storeLoop (value : Bool) (next : Λ) (state : State q)
    (base : Tape → List Bool) :
    TM2.stepAux (storeLoop value next) state base =
      ⟨some next, normal state.1.2 value, base⟩ := rfl

def nextRow (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .push .edge (fun _ => true)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

theorem stepAux_nextRow (next : Λ) (state : State q)
    (base : Tape → List Bool) (edge : Nat) (suffix : List Bool)
    (he : base .edge = encodeWord edge ++ suffix) :
    TM2.stepAux (nextRow next) state base =
      ⟨some next, (state.1, none),
        Function.update base .edge (encodeWord (edge + 1) ++ suffix)⟩ := by
  simp [nextRow, TM2.stepAux, he, encodeWord, List.replicate_succ]

def transportInTime {K τ υ : Type} [DecidableEq K] {Γ : K → Type}
    (e : τ ≃ υ) (p : Λ → TM2.Stmt Γ Λ τ)
    {start finish : TM2.Cfg Γ Λ τ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step p) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step (MachineControl.program (Equiv.refl Λ) e p))
      (MachineControl.configuration id e start)
      (some (MachineControl.configuration id e finish)) budget := by
  apply MachineComposition.liftExecutionInTime _ _ (MachineControl.configuration id e) _ run
  intro a b hab
  have h := MachineControl.step_simulation (Equiv.refl Λ) e p a
  rw [hab] at h
  exact h

end IndependentSetsGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
