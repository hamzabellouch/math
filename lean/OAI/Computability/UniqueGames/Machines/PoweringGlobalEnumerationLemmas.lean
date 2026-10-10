import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryEqualityBit
import OAI.Computability.UniqueGames.Machines.PoweringMachineEqualityField
import OAI.Computability.UniqueGames.Machines.PoweringMachineInitialize
import OAI.Computability.UniqueGames.Machines.PoweringMachineRelationLemmas
import OAI.Computability.UniqueGames.PCP.PoweringLabelsLemmas
import OAI.Computability.UniqueGames.PCP.PoweringTablesLemmas

namespace OAI

/-!
# Explicit executable enumeration of the global powering tapes

The four header tapes come first, followed by the eleven shared roles, the
bounded trajectory tapes, and the final output tape. Both directions use
constructor cases and arithmetic sum encodings. No enumeration is selected
from a cardinality theorem.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The single extra output tape occupies its unique local index. -/
def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

/-- Exact arithmetic numbering of every physical global tape. -/
def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

/-- The executable equivalence consumed by Finish and DrainMany. -/
def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

theorem sharedRole_index (max : Nat) (i : Fin 11) :
    (globalTapeEquiv max (.inr (.inl (.inl i)))).val = 4 + i.val := rfl

theorem trajectory_index (max : Nat) (i : Fin max) :
    (globalTapeEquiv max (.inr (.inl (.inr i)))).val = 4 + (11 + i.val) := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

/-- The exact cardinality follows from the explicit executable bijection. -/
theorem card_globalTape (max : Nat) :
    Fintype.card (GlobalTape max) = 4 + (11 + max + 1) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (globalTapeEquiv max)

theorem natCard_globalTape (max : Nat) :
    Nat.card (GlobalTape max) = 4 + (11 + max + 1) := by
  simpa only [Nat.card_fin] using Nat.card_congr (globalTapeEquiv max)

/-- A fixed finite list of all tape names is available without ambient search. -/
def allTapes (max : Nat) : List (GlobalTape max) := List.ofFn (enumeration max)

theorem allTapes_length (max : Nat) : (allTapes max).length = 4 + (11 + max + 1) := by
  simpa only [allTapes] using (List.length_ofFn (f := enumeration max))

theorem mem_allTapes (max : Nat) (tape : GlobalTape max) : tape ∈ allTapes max := by
  change tape ∈ List.ofFn (enumeration max)
  apply List.mem_ofFn.mpr
  exact ⟨globalTapeEquiv max tape, enumeration_globalTapeEquiv max tape⟩

end UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalEnumeration

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := MachineUnaryEqualityBit.State A
abbrev Label (path : List (Fin d)) := PoweringMachineWord.Label path.length ⊕ MachineAffineLookup.Label

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

omit [DecidableEq K] in
theorem lookupTapes_injective (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) : Function.Injective (lookupTapes placement) := by
  intro i j h
  exact (Fin.succ_injective _) ((PoweringMachineTapes.relationPlacement_injective max) (distinct h))

omit [DecidableEq K] in
theorem source_outside_lookup (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) :
    ∀ i, placement (.inl 6) ≠ lookupTapes placement i := by
  intro i h
  have heq : PoweringMachineTapes.relationPlacement max 0 = PoweringMachineTapes.relationPlacement max i.succ := by
    simpa [PoweringMachineTapes.leftEndpoint] using distinct h
  have hi := (PoweringMachineTapes.relationPlacement_injective max) heq
  have hv := congrArg Fin.val hi
  simp at hv

def endpoint (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d)) : Fin n :=
  PoweringWalks.walkEnd (PortTables.portGraph table) vertex path

theorem endpoint_eq_wordEnd (table : PortTables.Table n d) (vertex : Fin n)
    (path : List (Fin d)) :
    endpoint table vertex path =
      PoweringWalks.wordEnd (PortTables.portGraph table) path.length vertex path.get := by
  rw [PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
  rfl

def bit (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d))
    (port : Fin d) (left right : PortTables.Label) : Nat :=
  GraphTables.bitWord (PortTables.accepts table (endpoint table vertex path, port) left right)

def instruction (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ) :
    Label path → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
      path.get (fun z => labels (.inl z)) (some (labels (.inr .seed))) q
  | .inr q => PoweringMachineRelation.instruction (placement (.inl 6)) (lookupTapes placement)
      port (GraphTables.relationIndex (left, right)) (fun z => labels (.inr z)) exit q

def afterWord (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (table : PortTables.Table n d)
    (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    vertex path.get base

def finalTapes (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (lookupTapes placement)
    (afterWord placement path lengthBound table vertex base) (PortTables.tableWords table)
    (PoweringMachineRelation.address (endpoint table vertex path) port
      (GraphTables.relationIndex (left, right))) (bit table vertex path port left right)

def steps (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) : Nat :=
  PoweringMachineWord.steps table path.length vertex path.get +
    MachineAffineLookup.steps (PortTables.tableWords table) (endpoint table vertex path).val
      (4098 * d) (4098 * port.val + 4 + (GraphTables.relationIndex (left, right)).val)

theorem afterWord_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4) (h₆ : role ≠ 6) :
    afterWord placement path lengthBound table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  apply PoweringMachineWord.finalTapes_other
  · intro h; exact h₂ (by simpa [PoweringMachineTapes.query] using distinct h)
  · intro h; exact h₃ (by simpa [PoweringMachineTapes.scan] using distinct h)
  · intro h; exact h₄ (by simpa [PoweringMachineTapes.reverse] using distinct h)
  · intro h; exact h₆ (by simpa [PoweringMachineTapes.leftEndpoint] using distinct h)
  · intro i h
    have heq := distinct h
    simp at heq

/-- Table, start, scratch and both comparison stacks satisfy these numerical
inequalities, so their contents are preserved without an emptiness premise. -/
theorem finalTapes_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4)
    (h₆ : role ≠ 6) (h₁₀ : role ≠ 10) :
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  calc
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
        afterWord placement path lengthBound table vertex base (placement (.inl role)) := by
      apply MachineAffineLookup.finalTapes_other
      · intro h; exact h₂ (by simpa [lookupTapes, PoweringMachineTapes.query] using distinct h)
      · intro h; exact h₃ (by simpa [lookupTapes, PoweringMachineTapes.scan] using distinct h)
      · intro h; exact h₁₀ (by simpa [lookupTapes, PoweringMachineTapes.rowOutput] using distinct h)
    _ = _ := afterWord_frame placement distinct path lengthBound table vertex base role h₂ h₃ h₄ h₆

/-- Any caller tape outside the shared placement is preserved, including a
separate accumulator for already completed output rows. -/
theorem finalTapes_other (placement : PoweringMachineTapes.Tape max → K)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (k : K) (outside : ∀ i, k ≠ placement i) :
    finalTapes placement path lengthBound port left right table vertex base k = base k := by
  calc
    finalTapes placement path lengthBound port left right table vertex base k =
        afterWord placement path lengthBound table vertex base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (outside _) (outside _) (outside _)
    _ = base k := PoweringMachineWord.finalTapes_other _ _ _ _ _ _ _
      (outside _) (outside _) (outside _) (outside _) (fun i => outside _)

theorem fieldTrace (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement path lengthBound port left right labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 5)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix) (ambient : A) :
    (advance (TM2.step program))^[steps path port left right table vertex]
      (some ⟨some (labels (.inl (PoweringMachineWord.entry path.length))), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes placement path lengthBound port left right table vertex base⟩ ∧
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl 10)) =
      encodeWord (bit table vertex path port left right) ++ base (placement (.inl 10)) := by
  have hword := PoweringMachineWord.wordTrace table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective lengthBound false)) vertex path.get
    (fun q => labels (.inl q)) (some (labels (.inr .seed))) program
    (fun q => atLabels (.inl q)) base (by simpa [PoweringMachineTapes.table] using tableWord)
    (by simpa [PoweringMachineTapes.scratch] using scratchEmpty) suffix
    (by simpa [PoweringMachineTapes.start] using sourceWord) (ambient, false, none) none
  let mid := afterWord placement path lengthBound table vertex base
  have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 0
      (by decide) (by decide) (by decide) (by decide)]
    exact tableWord
  have hmidScratch : mid (placement (.inl 5)) = [] := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 5
      (by decide) (by decide) (by decide) (by decide)]
    exact scratchEmpty
  have hmidOutput : mid (placement (.inl 10)) = base (placement (.inl 10)) :=
    afterWord_frame placement distinct path lengthBound table vertex base 10
      (by decide) (by decide) (by decide) (by decide)
  have hmidEndpoint : mid (placement (.inl 6)) = encodeWord (endpoint table vertex path).val ++
      base (placement (.inl 6)) := by
    dsimp only [mid, afterWord]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five, PoweringMachineTapes.endpoint_false,
      PoweringMachineTapes.leftEndpoint, ← endpoint_eq_wordEnd] using hword.2
  have hrelation := PoweringMachineRelation.relationTrace (placement (.inl 6)) (lookupTapes placement)
    (lookupTapes_injective placement distinct) (source_outside_lookup placement distinct)
    port (GraphTables.relationIndex (left, right)) (fun q => labels (.inr q)) exit program
    (fun q => atLabels (.inr q)) table (endpoint table vertex path) mid
    (by simpa [lookupTapes, PoweringMachineTapes.table] using hmidTable)
    (by simpa [lookupTapes, PoweringMachineTapes.scratch] using hmidScratch)
    (base (placement (.inl 6))) hmidEndpoint (ambient, false, none) none
  constructor
  · simp only [MachineUnaryEqualityBit.clean]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, hword.1]
    exact hrelation
  · change MachineAffineLookup.finalTapes (lookupTapes placement) _ _ _ _ (lookupTapes placement 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord (bit table vertex path port left right) ++ mid (placement (.inl 10)) = _
    rw [hmidOutput]

theorem steps_le (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) :
    steps path port left right table vertex ≤
      (14 * path.length + 9) * (PortTables.tableBits table).length + 12 * path.length + 9 := by
  have hw := PoweringMachineWord.steps_le table path.length vertex path.get
  have hr := PoweringMachineRelation.steps_le table (endpoint table vertex path) port
    (GraphTables.relationIndex (left, right))
  simp only [steps, Nat.add_mul, Nat.mul_assoc] at hw ⊢
  omega

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRelationField

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

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

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

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

/-- Each command of the actual row plan has a fixed bound of twice the radius. -/
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

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachinePlan

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

/-- The existing word placement, with its result directed to row-output 10. -/
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

/-- Only the coefficient, word, and direction are built into finite control. -/
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

/-- Compose the actual affine and word/copy instructions. The trace and both
header values are derived; the only data premises describe the physical input. -/
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

/-- In particular, table 0, start 1, scratch 5, and saved endpoint/copy tapes
6--9 survive the header phase. Only roles 2, 3, 4, 10 and trajectory tapes may change. -/
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

/-- Linear in the serialized input length for the fixed word length. -/
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

/-- A closed finite-control instance. Embedded uses instantiate `instruction`
on the caller's common tapes and preserve its larger ambient register. -/
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

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRowHeaders

end OAI
