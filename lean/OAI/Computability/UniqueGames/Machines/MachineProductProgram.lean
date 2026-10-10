import OAI.Computability.UniqueGames.Games.ProductMachineSemantics
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineProductFieldLemmas
import OAI.Computability.UniqueGames.Machines.MachineProductSeed
import OAI.Computability.UniqueGames.PCP.SourceLoopInitLemmas
import OAI.Computability.UniqueGames.PCP.SourceQueryLoopLemmas

namespace OAI


namespace UniqueGamesTheorem.Explicit.MachineProductProgram

open Turing
open UniqueGamesTheorem.Foundations
open Complexity Hastad
open UniqueGamesTheorem.Reduction.MachineTransfer


abbrev Extra (t : Nat) := Fin 10 ⊕ Fin (t + 1)
abbrev Tape (t : Nat) := SourceContextLoad.Tape t (Extra t)
abbrev State := MachineHorner.State Unit

def auxiliary (t : Nat) (i : Fin 10) : Tape t := .extra (.inl i)
def constantDigit (t : Nat) (i : Fin (t + 1)) : Tape t := .extra (.inr i)
def accumulator (t : Nat) : Tape t := auxiliary t 6
def output (t : Nat) : Tape t := auxiliary t 9

def rowRole (t : Nat) : MachineProductRow.Layout t → Tape t
  | .inl (.inl (.inl 0)) => .formula
  | .inl (.inl (.inl 1)) => .index
  | .inl (.inl (.inl 2)) => .work
  | .inl (.inl (.inl 3)) => .scratch
  | .inl (.inl (.inr (.inl i))) => .current i
  | .inl (.inl (.inr (.inr i))) => .field i 0
  | .inl (.inr i) => auxiliary t (Fin.castLE (by omega) i)
  | .inr _ => auxiliary t 7

private def decodeRow (t : Nat) : Tape t → Option (MachineProductRow.Layout t)
  | .formula => some (.inl (.inl (.inl 0)))
  | .index => some (.inl (.inl (.inl 1)))
  | .work => some (.inl (.inl (.inl 2)))
  | .scratch => some (.inl (.inl (.inl 3)))
  | .current i => some (.inl (.inl (.inr (.inl i))))
  | .field i s => if s = 0 then some (.inl (.inl (.inr (.inr i)))) else none
  | .extra (.inl i) => if h : i.val < 7 then some (.inl (.inr ⟨i.val, h⟩))
      else if i = 7 then some (.inr ()) else none
  | _ => none

private theorem decodeRow_role (t : Nat) (i : MachineProductRow.Layout t) :
    decodeRow t (rowRole t i) = some i := by
  rcases i with (((i | (i | i)) | i) | i)
  · fin_cases i <;> rfl
  · rfl
  · simp [decodeRow, rowRole]
  · simp [rowRole, auxiliary, decodeRow, i.isLt]
  · cases i; rfl

def rowSlots (t : Nat) : MachineProductRow.Layout t ↪ Tape t where
  toFun := rowRole t
  inj' := by
    intro a b h
    have d := congrArg (decodeRow t) h
    exact Option.some.inj (by simpa only [decodeRow_role] using d)

def powerRole (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) → Tape t
  | .inl 0 => auxiliary t (if edgeCount then 8 else 0)
  | .inl 1 => auxiliary t 1
  | .inl 2 => auxiliary t 2
  | .inl 3 => auxiliary t 5
  | .inl 4 => auxiliary t 3
  | .inl 5 => auxiliary t 4
  | .inr i => constantDigit t i

theorem powerRole_injective (t : Nat) (edgeCount : Bool) : Function.Injective (powerRole t edgeCount) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> cases edgeCount <;> simp_all [powerRole, auxiliary]
    | inr b => fin_cases a <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
    | inr b => simpa [powerRole, constantDigit] using h

def powerSlots (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) ↪ Tape t :=
  ⟨powerRole t edgeCount, powerRole_injective t edgeCount⟩

def initRole (t : Nat) : MachineOdometerInit.Tape t → Tape t
  | .radix => auxiliary t 8
  | .scratch => .copyScratch
  | .current i => .current i
  | .remaining i => .remaining i

theorem initRole_injective (t : Nat) : Function.Injective (initRole t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [initRole, auxiliary]

def seedCommands (t : Nat) : List (MachineProductSeed.Command (Tape t)) :=
  List.ofFn (fun i : Fin (t + 1) => (constantDigit t i, encodeWord (MachineProductPower.digits i.val)))

noncomputable def clearKeys (t : Nat) : List (Tape t) :=
  Finset.univ.toList.filter (fun k => decide (k ≠ accumulator t ∧ k ≠ output t))

@[simp] theorem mem_clearKeys (t : Nat) (k : Tape t) :
    k ∈ clearKeys t ↔ k ≠ accumulator t ∧ k ≠ output t := by
  simp [clearKeys]

noncomputable section

inductive Label (q t : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | seedStart
  | seed (inner : MachineProductSeed.Label (seedCommands t))
  | power (edgeCount : Bool) (inner : MachineProductPower.Label t)
  | alphabetHeader
  | initialize (inner : MachineOdometerInit.Label t)
  | row (inner : MachineProductRow.Label (rowSlots t) (ProductMachineSemantics.commands q t))
  | check (i : Fin t)
  | reset (i : Fin t)
  | finishStart
  | finish (inner : SourceRuntimeFinish.Label (clearKeys t))
  deriving DecidableEq, Fintype

def headerDestination (t : Nat) : Fin 3 → Tape t
  | 0 => auxiliary t 0
  | 1 => auxiliary t 7
  | 2 => auxiliary t 8

def rowMain (q t : Nat) : Label q t :=
  .row (.inl (MachineProductRow.localMain (rowSlots t) (ProductMachineSemantics.sourceCommand t)))

def nextCheck (q t i : Nat) : Label q t := if h : i < t then .check ⟨i, h⟩ else .finishStart

def resetAt (q t i : Nat) : Label q t := if h : i < t then .reset ⟨i, h⟩ else .finishStart

def headerNext (q t : Nat) (i : Fin 3) : Label q t :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .seedStart

def program (q t : Nat) : Label q t → TM2.Stmt (fun _ : Tape t => Bool) (Label q t) State
  | .headerStart i => SourceMachine.fieldStart (headerDestination t i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .formula (headerDestination t i)
      (.headerRead i) (some (headerNext q t i))
  | .seedStart => exitAt .formula (MachineProductSeed.entry (seedCommands t) Label.seed
      (some (.power false (.inl .start))))
  | .seed inner => MachineProductSeed.instruction (seedCommands t) Label.seed
      (some (.power false (.inl .start))) inner
  | .power false inner => MachineProductPower.instruction (powerSlots t false) (accumulator t)
      (Label.power false) (some .alphabetHeader) inner
  | .power true inner => MachineProductPower.instruction (powerSlots t true) (accumulator t)
      (Label.power true) (some (MachineOdometerInit.labelAt Label.initialize 0)) inner
  | .alphabetHeader => UniqueGamesTheorem.Reduction.MachineSubstitution.pushWord (accumulator t)
      (encodeWord (q ^ t)) (.goto fun _ => .power true (.inl .start))
  | .initialize inner => MachineOdometerInit.statement (initRole t) Label.initialize
      (some (rowMain q t)) inner
  | .row inner => MachineProductRow.instruction (rowSlots t) (q + 2)
      (ProductMachineSemantics.commands q t) Label.row (some (nextCheck q t 0)) inner
  | .check i => MachineTupleOdometer.increment (.current i) (.remaining i)
      (rowMain q t) (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.remaining i)
      (.reset i) (nextCheck q t (i.val + 1))
  | .finishStart => exitAt .formula (SourceRuntimeFinish.entry (clearKeys t) Label.finish)
  | .finish inner => SourceRuntimeFinish.statement (clearKeys t) (accumulator t) (output t)
      ((), ()) Label.finish none inner

def machine (q t : Nat) : FinTM2 where
  K := Tape t
  k₀ := .formula
  k₁ := output t
  Γ _ := Bool
  Λ := Label q t
  main := .headerStart 0
  σ := State
  initialState := (((), ()), none)
  m := program q t

end

end UniqueGamesTheorem.Explicit.MachineProductProgram

end OAI
