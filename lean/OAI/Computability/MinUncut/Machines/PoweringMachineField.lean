import Mathlib
import OAI.Computability.MinUncut.Machines.PoweringMachineRelation
import OAI.Computability.MinUncut.PCP.PoweringRowData

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineField

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

end MinUncutGames.Foundations.Complexity.PoweringMachineField

namespace MinUncutGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev Command (d max : Nat) := {op : Instruction d // op.radius ≤ max}
abbrev LocalLabel (op : Command d max) := PoweringMachineField.Label op.val
abbrev Label (commands : List (Command d max)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel (fun op => PoweringMachineField.entry op.val)
    commands labels exit

def instruction (placement : PoweringMachineTapes.Tape max → K)
    (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A) :=
  MachineFiniteSequence.instruction LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    commands labels exit

def result (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (op : Command d max) (base : K → List Bool) : K → List Bool :=
  PoweringMachineField.finalTapes graph placement vertex op.val op.property base

def finalTapes (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf (result graph placement vertex) commands base

def steps (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph placement vertex)
    (fun op _ => PoweringMachineField.steps graph vertex op.val) commands base

theorem planTrace (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max))
    (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A))
    (atLabels : ∀ l, program (labels l) = instruction placement commands labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineField.Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph placement vertex commands base]
      (some ⟨entry commands labels exit, MachineUnaryEqualityBit.clean ambient, base⟩) =
    some ⟨exit, MachineUnaryEqualityBit.clean ambient,
      finalTapes graph placement vertex commands base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    (result graph placement vertex) (fun op _ => PoweringMachineField.steps graph vertex op.val)
    program (PoweringMachineField.Ready graph placement vertex suffix)
    (fun _ => MachineUnaryEqualityBit.clean ambient) id commands
  · intro op _ tapes good
    exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
      op.property tapes suffix good
  · intro op _ localLabels localExit atLocal tapes good
    exact PoweringMachineField.fieldTrace graph placement distinct vertex op.val op.property
      localLabels localExit program atLocal tapes suffix good ambient
  · exact atLabels
  · exact ready

theorem ready_finalTapes (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    PoweringMachineField.Ready graph placement vertex suffix
      (finalTapes graph placement vertex commands base) := by
  induction commands generalizing base with
  | nil => exact ready
  | cons op commands ih =>
      apply ih
      exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
        op.property base suffix ready

theorem finalTapes_output (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex commands base (placement (.inl 10)) =
      PoweringMachineRow.encodeBits ((commands.map (fun op => evaluate graph vertex op.val)).reverse) ++
        base (placement (.inl 10)) := by
  induction commands generalizing base with
  | nil => rfl
  | cons op commands ih =>
      have nextReady := PoweringMachineField.ready_finalTapes graph placement distinct vertex
        op.val op.property base suffix ready
      change finalTapes graph placement vertex commands
        (result graph placement vertex op base) (placement (.inl 10)) = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineField.finalTapes_output graph placement distinct vertex
        op.val op.property base suffix ready]
      simp only [List.map_cons, List.reverse_cons, PoweringMachineRow.encodeBits_append,
        PoweringMachineRow.encodeBits, List.append_nil,
        List.append_assoc]

def boundedRowPlan (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Command d (2 * (n + 1))) :=
  List.ofFn fun i : Fin (PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n)) =>
    let pair := (PoweringMachineRow.inputEquiv (n + 1) (PoweringRowData.slotCount d n)).symm i
    ⟨directedFieldPlan n ports direction pair.1 pair.2,
      directedFieldPlan_radius n ports direction pair.1 pair.2⟩

theorem boundedRowPlan_values (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (boundedRowPlan n ports direction).map Subtype.val = rowPlan n ports direction := by
  rw [boundedRowPlan, rowPlan, List.map_ofFn]
  rfl

theorem rowPlan_output (graph : PortTables.Table vertices d)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (distinct : Function.Injective placement) (vertex : Fin vertices) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex (boundedRowPlan n ports direction).reverse base
      (placement (.inl 10)) =
      PoweringRowData.dataTape graph n (direction, vertex, ports) ++ base (placement (.inl 10)) := by
  rw [finalTapes_output graph placement distinct vertex _ base suffix ready]
  rw [List.map_reverse, List.reverse_reverse, PoweringFieldPlan.dataTape_eq_plan]
  have h := congrArg (List.map (evaluate graph vertex)) (boundedRowPlan_values n ports direction)
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun bits => PoweringMachineRow.encodeBits bits ++ base (placement (.inl 10))) h

end MinUncutGames.Foundations.Complexity.PoweringMachinePlan

end OAI
