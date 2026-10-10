import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Machines.MachineCompare
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.PCP.GenericGraphTables

namespace OAI

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open UniqueGamesTheorem.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .cursor, .scan, .vertices, .darts,
  .counter, .edge, .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight,
  .reversed, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool

/-- Self-loop flag, comparison mismatch flag, and second head register. -/
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

/-- Store the result chosen by the actual comparison's equal/different exit.
This does not compare tape contents in a register transition. -/
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

/-- One-step simulations transport complete timed executions through the
explicit finite register permutations. -/
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

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
