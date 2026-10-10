import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Emitter
import OAI.Combinatorics.IndependentSets.Machines.MachinePreservingLookupClean
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderRowControl
import OAI.Combinatorics.IndependentSets.Machines.MachineFixedDivMod

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Tape
  | inputVertex | table | output
  | emitScratch | queryReverse | queryIndex
  | lookupOutput | lookupWork | lookupRestore
  | quotientFirst | quotientSecond | remainderFirst | remainderSecond
  deriving DecidableEq

instance : Fintype Tape where
  elems := {.inputVertex, .table, .output, .emitScratch, .queryReverse, .queryIndex,
    .lookupOutput, .lookupWork, .lookupRestore, .quotientFirst, .quotientSecond,
    .remainderFirst, .remainderSecond}
  complete tape := by cases tape <;> simp

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

end IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

end OAI
