import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineRelationField
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineEqualityField
import OAI.Combinatorics.IndependentSets.Expansion.PoweringFieldPlan

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape
abbrev State := MachineUnaryEqualityBit.State

def Label : Instruction d → Type
  | .relation path _ _ _ => PoweringMachineRelationField.Label path
  | .equal left right => PoweringMachineEqualityField.Label left.length right.length

instance labelFintype (op : Instruction d) : Fintype (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

instance labelDecidableEq (op : Instruction d) : DecidableEq (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

def entry : (op : Instruction d) → Label op
  | .relation path _ _ _ => .inl (PoweringMachineWord.entry path.length)
  | .equal left right => PoweringMachineEqualityField.entry left.length right.length

def instruction (placement : Tape max → K) : (op : Instruction d) → op.radius ≤ max →
    (Label op → Λ) → Option Λ → Label op → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .relation path port a b, bounded, labels, exit =>
      PoweringMachineRelationField.instruction placement path bounded port a b labels exit
  | .equal left right, bounded, labels, exit =>
      PoweringMachineEqualityField.instruction
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement left.get right.get labels exit

def finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) : (op : Instruction d) → op.radius ≤ max →
      (K → List Bool) → K → List Bool
  | .relation path port a b, bounded, base =>
      PoweringMachineRelationField.finalTapes placement path bounded port a b graph vertex base
  | .equal left right, bounded, base =>
      PoweringMachineEqualityField.finalTapes graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement vertex left.get right.get base

def steps (graph : PortTables.Table n d) (vertex : Fin n) : Instruction d → Nat
  | .relation path port a b => PoweringMachineRelationField.steps path port a b graph vertex
  | .equal left right => PoweringMachineEqualityField.steps graph vertex left.get right.get

structure Ready (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (suffix : List Bool) (tapes : K → List Bool) : Prop where
  table : tapes (placement (.inl 0)) = PortTables.tableBits graph
  source : tapes (placement (.inl 1)) = encodeWord vertex.val ++ suffix
  scratch : tapes (placement (.inl 5)) = []
  leftCopy : tapes (placement (.inl 8)) = []
  rightCopy : tapes (placement (.inl 9)) = []

theorem finalTapes_role (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (j : Fin 11) (role : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph placement vertex op bounded base (placement (.inl j)) =
      base (placement (.inl j)) := by
  cases op with
  | relation path port a b =>
      apply PoweringMachineRelationField.finalTapes_frame placement distinct path bounded
        port a b graph vertex base j
      all_goals rcases role with rfl | rfl | rfl | rfl | rfl <;> decide
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_role graph _ _ placement distinct
        vertex left.get right.get base j role

theorem ready_finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    Ready graph placement vertex suffix (finalTapes graph placement vertex op bounded base) := by
  constructor
  · rw [finalTapes_role graph placement distinct vertex op bounded base 0 (by simp)]
    exact ready.table
  · rw [finalTapes_role graph placement distinct vertex op bounded base 1 (by simp)]
    exact ready.source
  · rw [finalTapes_role graph placement distinct vertex op bounded base 5 (by simp)]
    exact ready.scratch
  · rw [finalTapes_role graph placement distinct vertex op bounded base 8 (by simp)]
    exact ready.leftCopy
  · rw [finalTapes_role graph placement distinct vertex op bounded base 9 (by simp)]
    exact ready.rightCopy

theorem finalTapes_other (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (op : Instruction d) (bounded : op.radius ≤ max)
    (base : K → List Bool) (k : K) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph placement vertex op bounded base k = base k := by
  cases op with
  | relation path port a b =>
      exact PoweringMachineRelationField.finalTapes_other placement path bounded port a b
        graph vertex base k outside
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_other graph _ _ placement vertex
        left.get right.get base k (outside _) (outside _) (outside _) (outside _)
        (outside _) (outside _) (fun i => outside _)

theorem fieldTrace (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max)
    (labels : Label op → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement op bounded labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex op]
      (some ⟨some (labels (entry op)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph placement vertex op bounded base⟩ := by
  cases op with
  | relation path port a b =>
      exact (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        labels exit program atLabels graph vertex base ready.table ready.scratch suffix
        ready.source ambient).1
  | equal left right =>
      exact PoweringMachineEqualityField.fieldTrace graph _ _ placement distinct
        vertex left.get right.get labels exit program atLabels base ready.table ready.scratch
        ready.leftCopy ready.rightCopy suffix ready.source ambient

theorem finalTapes_output (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex op bounded base (placement (.inl 10)) =
      PoweringMachineRow.encodeBit (evaluate graph vertex op) ++ base (placement (.inl 10)) := by
  cases op with
  | relation path port a b =>
      have h := (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        id none (PoweringMachineRelationField.instruction placement path bounded port a b id none)
        (fun _ => rfl) graph vertex base ready.table ready.scratch suffix ready.source ()).2
      have he : ∀ bit : Bool, encodeWord (GraphTables.bitWord bit) =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineRelationField.bit, PoweringMachineRelationField.endpoint,
        evaluate, he] using h
  | equal left right =>
      have h := PoweringMachineEqualityField.finalTapes_output graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded) placement distinct
        vertex left.get right.get base
      have he : ∀ bit : Bool, MachineUnaryEqualityBit.bitEncoding bit =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineEqualityField.resultBit, PoweringMachineEqualityField.endpoint,
        PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get, evaluate, he] using h

end IndependentSetsGames.Foundations.Complexity.PoweringMachineField

end OAI
