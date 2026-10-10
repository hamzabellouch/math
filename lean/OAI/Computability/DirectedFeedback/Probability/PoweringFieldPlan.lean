import Mathlib
import OAI.Computability.DirectedFeedback.Machines.PoweringMachineRelationField

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open DFVSGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

def tailPorts : (n : Nat) → (Fin (n + 1) → D) → Fin (n + 1) → List D
  | 0, _, _ => []
  | n + 1, p, k => Fin.cases [] (fun j => p 0 :: tailPorts n (fun i => p i.succ) j) k

theorem tailPorts_length : ∀ (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
    (tailPorts n p k).length = k.val := by
  intro n
  induction n with
  | zero => intro p k; have hk := Fin.eq_zero k; subst k; rfl
  | succ n ih =>
      intro p k
      refine Fin.cases rfl (fun j => ?_) k
      simp only [tailPorts, Fin.cases_succ, List.length_cons, ih, Fin.val_succ]

theorem walkEnd_tailPorts (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (p : Fin (n + 1) → D) (k : Fin (n + 1)),
      walkEnd G v (tailPorts n p k) = (edgeAt G n (v, p) k).1 := by
  intro n
  induction n with
  | zero => intro v p k; rfl
  | succ n ih =>
      intro v p k
      refine Fin.cases rfl (fun j => ?_) k
      exact ih (next G v (p 0)) (fun i => p i.succ) j

def headPorts (n : Nat) (p : Fin (n + 1) → D) (k : Fin (n + 1)) : List D :=
  tailPorts n p k ++ [p k]

theorem walkEnd_headPorts (G : PortGraph V D) (n : Nat) (v : V)
    (p : Fin (n + 1) → D) (k : Fin (n + 1)) :
    walkEnd G v (headPorts n p k) = (G.rot (edgeAt G n (v, p) k)).1 := by
  rw [headPorts, walkEnd_append, walkEnd_tailPorts]
  change (G.rot ((edgeAt G n (v, p) k).1, p k)).1 = _
  have hp : (edgeAt G n (v, p) k).2 = p k := edgeAt_port G n (v, p) k
  rw [← hp]

def addressPorts {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) : List (Fin d) :=
  List.ofFn ((allAddresses d t).get i).2

theorem walkEnd_addressPorts {d t : Nat} (G : PortGraph V (Fin d)) (v : V)
    (i : PoweringOpinionTables.AddressIndex d t) :
    walkEnd G v (addressPorts i) = (wordToBall G t v ((allAddresses d t).get i)).val :=
  (wordEnd_eq_walkEnd_ofFn G _ _ _).symm

inductive Instruction (d : Nat) where
  | relation (ports : List (Fin d)) (port : Fin d) (left right : Fin 64)
  | equal (left right : List (Fin d))

def Instruction.radius {d : Nat} : Instruction d → Nat
  | .relation ports _ _ _ => ports.length
  | .equal left right => max left.length right.length

theorem addressPorts_length_le {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) :
    (addressPorts i).length ≤ t := by
  simp only [addressPorts, List.length_ofFn]
  exact Nat.le_of_lt_succ ((allAddresses d t).get i).1.isLt

def evaluate {vertices d : Nat} (input : PortTables.Table vertices d)
    (start : Fin vertices) : Instruction d → Bool
  | .relation ports port a b => PortTables.accepts input
      (walkEnd (PortTables.portGraph input) start ports, port) a b
  | .equal left right => decide
      (walkEnd (PortTables.portGraph input) start left =
        walkEnd (PortTables.portGraph input) start right)

def fieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) : Field (slotCount d n) → Instruction d
  | .inl (a, b) => .relation (tailPorts n ports k) (ports k) a b
  | .inr (.inl i) => .equal (addressPorts i) (tailPorts n ports k)
  | .inr (.inr i) => .equal (List.ofFn ports ++ addressPorts i) (headPorts n ports k)

theorem evaluate_fieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (fieldPlan n ports k field) = walkData input n (start, ports) k field := by
  rcases field with ⟨a,b⟩ | i | i
  · simp only [evaluate, fieldPlan, walkData, walkEnd_tailPorts]
    have hp : (edgeAt (PortTables.portGraph input) n (start, ports) k).2 = ports k :=
      edgeAt_port (PortTables.portGraph input) n (start, ports) k
    rw [← hp]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_tailPorts]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input) start i
    rw [ha]
  · simp only [evaluate, fieldPlan, walkData, endpointMask, walkEnd_append,
      walkEnd_headPorts]
    rw [← wordEnd_eq_walkEnd_ofFn]
    have ha := walkEnd_addressPorts (t := n + 1) (PortTables.portGraph input)
      (wordEnd (PortTables.portGraph input) (n + 1) start ports) i
    rw [ha]
    rfl

def directedFieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) : Instruction d :=
  fieldPlan n ports k (if direction then transposeField field else field)

theorem fieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (fieldPlan n ports k field).radius ≤ 2 * (n + 1) := by
  have hk := k.isLt
  rcases field with ⟨a,b⟩ | i | i
  · simp only [fieldPlan, Instruction.radius, tailPorts_length]
    omega
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, tailPorts_length]
    exact max_le (by omega) (by omega)
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, headPorts, List.length_append,
      List.length_ofFn, List.length_singleton, tailPorts_length]
    exact max_le (by omega) (by omega)

theorem directedFieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (directedFieldPlan n ports direction k field).radius ≤ 2 * (n + 1) :=
  fieldPlan_radius n ports k _

theorem evaluate_directedFieldPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    evaluate input start (directedFieldPlan n ports direction k field) =
      rowData input n (direction, start, ports) k field :=
  evaluate_fieldPlan input n start ports k _

def rowPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Instruction d) :=
  List.ofFn fun i : Fin (inputSize (n + 1) (slotCount d n)) =>
    let pair := (inputEquiv (n + 1) (slotCount d n)).symm i
    directedFieldPlan n ports direction pair.1 pair.2

theorem evaluate_rowPlan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (rowPlan n ports direction).map (evaluate input start) =
      List.ofFn (rowBits input n (direction, start, ports)) := by
  rw [rowPlan, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [evaluate_directedFieldPlan, rowBits_packData]
  rfl

theorem dataTape_eq_plan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    dataTape input n (direction, start, ports) =
      encodeBits ((rowPlan n ports direction).map (evaluate input start)) := by
  rw [evaluate_rowPlan, dataTape_eq]

end DFVSGames.Foundations.PCP.PoweringFieldPlan
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineField

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

end DFVSGames.Foundations.Complexity.PoweringMachineField
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachinePlan

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

end DFVSGames.Foundations.Complexity.PoweringMachinePlan
end

section

namespace DFVSGames.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

def fieldBudget (max inputLength : Nat) : Nat :=
  (28 * max + 10) * inputLength + 24 * max + 15

theorem field_steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (op : Instruction d) (bounded : op.radius ≤ max) :
    PoweringMachineField.steps graph vertex op ≤
      fieldBudget max (PortTables.tableBits graph).length := by
  cases op with
  | relation path port left right =>
      change path.length ≤ max at bounded
      have h := PoweringMachineRelationField.steps_le path port left right graph vertex
      have coefficient : 14 * path.length + 9 ≤ 28 * max + 10 := by omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineRelationField.steps path port left right graph vertex ≤ _
      unfold fieldBudget
      omega
  | equal left right =>
      change Nat.max left.length right.length ≤ max at bounded
      have hl : left.length ≤ max := (le_max_left _ _).trans bounded
      have hr : right.length ≤ max := (le_max_right _ _).trans bounded
      have h := PoweringMachineEqualityField.steps_le graph vertex left.get right.get
      have coefficient : 14 * (left.length + right.length) + 10 ≤ 28 * max + 10 := by
        omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineEqualityField.steps graph vertex left.get right.get ≤ _
      unfold fieldBudget
      omega

theorem plan_steps_le (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (commands : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex commands base ≤
      commands.length * fieldBudget max (PortTables.tableBits graph).length := by
  induction commands generalizing base with
  | nil => simp only [PoweringMachinePlan.steps, MachineFiniteSequence.steps,
      List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons op commands ih =>
      have first := field_steps_le graph vertex op.val op.property
      have rest := ih (PoweringMachinePlan.result graph placement vertex op base)
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex commands
          (PoweringMachinePlan.result graph placement vertex op base) ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add first rest

@[simp] theorem boundedRowPlan_length (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringMachinePlan.boundedRowPlan n ports direction).length =
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) := by
  simp only [PoweringMachinePlan.boundedRowPlan, List.length_ofFn]

def rowBudget (d n inputLength : Nat) : Nat :=
  PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
    fieldBudget (2 * (n + 1)) inputLength

theorem rowPlan_steps_le (graph : PortTables.Table vertices d) (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (vertex : Fin vertices) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex
        (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base ≤
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
        ((28 * (2 * (n + 1)) + 10) * (PortTables.tableBits graph).length +
          24 * (2 * (n + 1)) + 15) := by
  have h := plan_steps_le graph placement vertex
    (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base
  simpa only [List.length_reverse, boundedRowPlan_length, fieldBudget] using h

def planInTime (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (PoweringMachinePlan.Command d max))
    (labels : PoweringMachinePlan.Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A))
    (atLabels : ∀ l, program (labels l) =
      PoweringMachinePlan.instruction placement commands labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineField.Ready graph placement vertex suffix base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨PoweringMachinePlan.entry commands labels exit, MachineUnaryEqualityBit.clean ambient, base⟩
      (some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        PoweringMachinePlan.finalTapes graph placement vertex commands base⟩)
      (commands.length * fieldBudget max (PortTables.tableBits graph).length) where
  steps := PoweringMachinePlan.steps graph placement vertex commands base
  evals_in_steps := PoweringMachinePlan.planTrace graph placement distinct vertex commands
    labels exit program atLabels base suffix ready ambient
  steps_le_m := plan_steps_le graph placement vertex commands base

def rowPlanInTime (graph : PortTables.Table vertices d) (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (distinct : Function.Injective placement) (vertex : Fin vertices)
    (labels : PoweringMachinePlan.Label
      (PoweringMachinePlan.boundedRowPlan n ports direction).reverse → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A))
    (atLabels : ∀ l, program (labels l) = PoweringMachinePlan.instruction placement
      (PoweringMachinePlan.boundedRowPlan n ports direction).reverse labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineField.Ready graph placement vertex suffix base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨PoweringMachinePlan.entry (PoweringMachinePlan.boundedRowPlan n ports direction).reverse
          labels exit, MachineUnaryEqualityBit.clean ambient, base⟩
      (some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        PoweringMachinePlan.finalTapes graph placement vertex
          (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base⟩)
      (rowBudget d n (PortTables.tableBits graph).length) where
  steps := PoweringMachinePlan.steps graph placement vertex
    (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base
  evals_in_steps := PoweringMachinePlan.planTrace graph placement distinct vertex
    (PoweringMachinePlan.boundedRowPlan n ports direction).reverse
    labels exit program atLabels base suffix ready ambient
  steps_le_m := rowPlan_steps_le graph n ports direction placement vertex base

end DFVSGames.Foundations.Complexity.PoweringPlanBudget
end

section

namespace DFVSGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open DFVSGames.Foundations.Complexity

variable {vertices d : Nat}

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

def reverseValue (d n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  blockSize d n * vertex.val + reverseOffset d n ports direction

def tailVertex (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Fin vertices :=
  if direction then wordEnd (PortTables.portGraph input) (n + 1) vertex ports else vertex

def headerWords (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  [(tailVertex input n vertex ports direction).val, reverseValue d n vertex ports direction]

theorem table_tail (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n (direction, vertex, ports)].tail =
      tailVertex input n vertex ports direction := by
  change (GenericGraphTables.semantics (PoweringTables.table input n)).tail
    (encodeDart vertices d n (direction, vertex, ports)) = _
  rw [PoweringTables.semantics_table]
  change (PoweringTables.mathematicalGraph input n).tail
    ((dartEquiv vertices d n).symm (dartEquiv vertices d n (direction, vertex, ports))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem table_reverseValue (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringTables.table input n).rows[encodeDart vertices d n
      (direction, vertex, ports)].reverseIndex.val = reverseValue d n vertex ports direction := by
  change (GenericGraphTables.reverseAt (PoweringTables.table input n).rows
    (encodeDart vertices d n (direction, vertex, ports))).val = _
  rw [PoweringTables.table_reverse, encodeDart, dartEquiv_val]
  cases direction <;>
    simp [reverseValue, blockSize, reverseOffset, orientationEquiv, Nat.add_assoc] <;> decide

theorem headerWords_eq (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    headerWords input n vertex ports direction =
      [(PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].tail.val,
       (PoweringTables.table input n).rows[encodeDart vertices d n
        (direction, vertex, ports)].reverseIndex.val] := by
  rw [table_tail, table_reverseValue]
  rfl

theorem header_relation_bits (input : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (suffix : List Bool) :
    encodeWords (headerWords input n vertex ports direction) ++
      (encodeWords (GenericGraphTables.relationWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)].relation) ++ suffix) =
      encodeWords (GenericGraphTables.rowWords
        (PoweringTables.table input n).rows[encodeDart vertices d n
          (direction, vertex, ports)]) ++ suffix := by
  rw [headerWords_eq, ← List.append_assoc, ← encodeWords_append]
  rfl

end DFVSGames.Foundations.PCP.PoweringRowHeaderSemantics
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

theorem headerPlacement_injective {t max : Nat} (h : t ≤ max) :
    Function.Injective (headerPlacement h) :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)).injective.comp (wordPlacement_injective h false)

@[simp] theorem headerPlacement_table {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 0) = table max := by
  simp [headerPlacement, table, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_query {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 1) = query max := by
  simp [headerPlacement, query, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scan {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 2) = scan max := by
  simp [headerPlacement, scan, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_reverse {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 3) = reverse max := by
  simp [headerPlacement, reverse, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scratch {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 4) = scratch max := by
  simp [headerPlacement, scratch, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_output {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 5) = rowOutput max := by
  simp [headerPlacement]

@[simp] theorem headerPlacement_start {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inr (PoweringMachineWord.first t)) = start max := by
  simp [headerPlacement, start, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_succ {t max : Nat} (h : t ≤ max) (i : Fin t) :
    headerPlacement h (.inr i.succ) = .inr (Fin.castLE h i) := by
  simp [headerPlacement, leftEndpoint, rowOutput, Equiv.swap_apply_def]

abbrev Label (n : Nat) := MachineUnaryAffineAt.Label ⊕
  (MachineUnaryAffineAt.Label ⊕ PoweringMachineWord.Label (n + 1))

def entry (n : Nat) : Label n := .inl .seed

def tailEntry (n : Nat) (direction : Bool) : Label n :=
  if direction then .inr (.inr (PoweringMachineWord.entry (n + 1))) else .inr (.inl .seed)

def affineInstruction (source work output : K) (coefficient offset : Nat)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source work output coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt work source id false (labels .restore) exit

def instruction (n : Nat) (h : n + 1 ≤ max) (placement : Tape max → K)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl q => affineInstruction (placement (start max)) (placement (scratch max))
      (placement (rowOutput max)) (blockSize d n) (reverseOffset d n ports direction)
      (fun z => labels (.inl z)) (some (labels (tailEntry n direction))) q
  | .inr (.inl q) => PoweringMachineWord.copyInstruction
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (fun z => labels (.inr (.inl z))) exit q
  | .inr (.inr q) => PoweringMachineWord.instruction (n + 1)
      (placement ∘ headerPlacement h) ports (fun z => labels (.inr (.inr z))) exit q

def afterReverse (n : Nat) (placement : Tape max → K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  Function.update base (placement (rowOutput max))
    (encodeWord (reverseValue d n vertex ports direction) ++ base (placement (rowOutput max)))

def finalTapes (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterReverse n placement vertex ports direction base
  if direction then
    PoweringMachineWord.finalTapes input (n + 1) (placement ∘ headerPlacement h) vertex ports mid
  else Function.update mid (placement (rowOutput max))
    (encodeWord vertex.val ++ mid (placement (rowOutput max)))

def steps (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  (2 * (vertex.val + 1) + 1) +
    if direction then PoweringMachineWord.steps input (n + 1) vertex ports
    else 2 * (vertex.val + 1) + 1

theorem headerTrace (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction n h placement ports direction labels exit l)
    (base : K → List Bool) (tableWord : base (placement (table max)) = PortTables.tableBits input)
    (scratchEmpty : base (placement (scratch max)) = []) (suffix : List Bool)
    (sourceWord : base (placement (start max)) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps input n vertex ports direction]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes input n h placement vertex ports direction base⟩ ∧
    finalTapes input n h placement vertex ports direction base (placement (rowOutput max)) =
      encodeWords (headerWords input n vertex ports direction) ++ base (placement (rowOutput max)) := by
  have hd (i j : Tape max) (hne : i ≠ j) : placement i ≠ placement j :=
    fun eq => hne (distinct eq)
  have hsourceOut : placement (start max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [start, rowOutput])
  have hscratchOut : placement (scratch max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [scratch, rowOutput])
  have htableOut : placement (table max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [table, rowOutput])
  let mid := afterReverse n placement vertex ports direction base
  have hrev := MachineUnaryAffineAt.seededAffineTrace
    (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
    (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut
    (blockSize d n) (reverseOffset d n ports direction)
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (tailEntry n direction))) program
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base vertex.val suffix sourceWord scratchEmpty ambient register
  have hreverseTrace : (advance (TM2.step program))^[2 * (vertex.val + 1) + 1]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨some (labels (tailEntry n direction)), (ambient, none), mid⟩ := by
    simpa only [entry, mid, afterReverse, reverseValue] using hrev
  have hmidSource : mid (placement (start max)) = encodeWord vertex.val ++ suffix := by
    simpa only [mid, afterReverse, Function.update_of_ne hsourceOut] using sourceWord
  have hmidScratch : mid (placement (scratch max)) = [] := by
    simpa only [mid, afterReverse, Function.update_of_ne hscratchOut] using scratchEmpty
  have hmidTable : mid (placement (table max)) = PortTables.tableBits input := by
    simpa only [mid, afterReverse, Function.update_of_ne htableOut] using tableWord
  cases direction with
  | false =>
    have hcopy := MachineUnaryAffineAt.seededAffineTrace
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut 1 0
      (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
      (labels (.inr (.inl .restore))) exit program
      (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
      (atLabels (.inr (.inl .restore))) mid vertex.val suffix hmidSource hmidScratch ambient none
    constructor
    · rw [steps, ite_eq_right Bool.false_ne_true, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, Bool.false_eq_true, ite_false, finalTapes, Nat.one_mul,
        Nat.add_zero] using hcopy
    · simp only [finalTapes, Bool.false_eq_true, ite_false, Function.update_self,
        afterReverse, headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc]
  | true =>
    have hword := PoweringMachineWord.wordTrace input (n + 1)
      (placement ∘ headerPlacement h) (distinct.comp (headerPlacement_injective h)) vertex ports
      (fun z => labels (.inr (.inr z))) exit program (fun z => atLabels (.inr (.inr z))) mid
      (by simpa only [Function.comp_apply, headerPlacement_table] using hmidTable)
      (by simpa only [Function.comp_apply, headerPlacement_scratch] using hmidScratch)
      suffix (by simpa only [Function.comp_apply, headerPlacement_start] using hmidSource) ambient none
    constructor
    · rw [steps, ite_eq_left rfl, Nat.add_comm, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, ite_true, finalTapes] using hword.1
    · have hout := hword.2
      simp only [Function.comp_apply, headerPlacement_output] at hout
      simpa only [finalTapes, ite_true, mid, afterReverse, Function.update_self,
        headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc] using hout

theorem finalTapes_other (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (query max)) (hscan : k ≠ placement (scan max))
    (hreverse : k ≠ placement (reverse max)) (houtput : k ≠ placement (rowOutput max))
    (hpositions : ∀ i : Fin (n + 1), k ≠ placement (.inr (Fin.castLE h i))) :
    finalTapes input n h placement vertex ports direction base k = base k := by
  cases direction with
  | false => simp only [finalTapes, Bool.false_eq_true, ite_false,
      Function.update_of_ne houtput, afterReverse]
  | true =>
    let mid := afterReverse n placement vertex ports true base
    have hw := PoweringMachineWord.finalTapes_other input (n + 1)
      (placement ∘ headerPlacement h) vertex ports mid k
      (by simpa only [Function.comp_apply, headerPlacement_query] using hquery)
      (by simpa only [Function.comp_apply, headerPlacement_scan] using hscan)
      (by simpa only [Function.comp_apply, headerPlacement_reverse] using hreverse)
      (by simpa only [Function.comp_apply, headerPlacement_output] using houtput)
      (fun i => by simpa only [Function.comp_apply, headerPlacement_succ] using hpositions i)
    calc
      _ = mid k := hw
      _ = base k := by simp only [mid, afterReverse, Function.update_of_ne houtput]

theorem finalTapes_shared (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (i : Fin 11)
    (hquery : i ≠ 2) (hscan : i ≠ 3) (hreverse : i ≠ 4) (houtput : i ≠ 10) :
    finalTapes input n h placement vertex ports direction base (placement (.inl i)) =
      base (placement (.inl i)) := by
  apply finalTapes_other input n h placement vertex ports direction base
  · intro heq; exact hquery (Sum.inl.inj (distinct heq))
  · intro heq; exact hscan (Sum.inl.inj (distinct heq))
  · intro heq; exact hreverse (Sum.inl.inj (distinct heq))
  · intro heq; exact houtput (Sum.inl.inj (distinct heq))
  · intro j heq; cases distinct heq

theorem steps_le (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps input n vertex ports direction ≤
      (14 * (n + 1) + 4) * (PortTables.tableBits input).length + 12 * (n + 1) + 6 := by
  have hv : vertex.val ≤ (PortTables.tableBits input).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length input)
  have hw := PoweringMachineWord.steps_le input (n + 1) vertex ports
  cases direction <;> simp only [steps, Bool.false_eq_true, ite_false, ite_true]
  · simp only [Nat.add_mul]
    omega
  · calc
      _ ≤ (2 * (PortTables.tableBits input).length + 3) +
          ((14 * (n + 1) + 2) * (PortTables.tableBits input).length + 12 * (n + 1) + 3) :=
        Nat.add_le_add (by omega) hw
      _ = _ := by simp only [Nat.add_mul]; omega

def machine (degree n : Nat) (ports : Fin (n + 1) → Fin degree) (direction : Bool) : FinTM2 where
  K := PoweringMachineTapes.Tape (n + 1)
  k₀ := table (n + 1)
  k₁ := rowOutput (n + 1)
  Γ _ := Bool
  Λ := Label n
  main := entry n
  σ := (Unit × Bool × Option Bool) × Option Bool
  initialState := (((), false, none), none)
  m := instruction n (Nat.le_refl (n + 1)) id ports direction id none

end DFVSGames.Foundations.Complexity.PoweringMachineRowHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
