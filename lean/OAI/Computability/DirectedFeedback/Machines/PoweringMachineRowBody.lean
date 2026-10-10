import Mathlib
import OAI.Computability.DirectedFeedback.Probability.PoweringFieldPlan

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

namespace DFVSGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev capacity (n : Nat) := 2 * (n + 1)
abbrev bufferSize (d n : Nat) := PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n)
abbrev State (d n : Nat) := PoweringMasterState.Master (bufferSize d n)

def commands (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :=
  (PoweringMachinePlan.boundedRowPlan n ports direction).reverse

abbrev Label (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :=
  PoweringMachinePlan.Label (commands n ports direction) ⊕
    (Unit ⊕ PoweringMachineRowHeaders.Label n)

def planMain {max : Nat} {E : Type}
    (ops : List (PoweringMachinePlan.Command d max)) (fallback : E) :
    PoweringMachinePlan.Label ops ⊕ E :=
  match ops with
  | [] => .inr fallback
  | op :: _ => .inl (.inl (PoweringMachineField.entry op.val))

theorem plan_entry_eq {max : Nat} {E : Type}
    (ops : List (PoweringMachinePlan.Command d max)) (fallback : E)
    (labels : PoweringMachinePlan.Label ops ⊕ E → Λ) :
    PoweringMachinePlan.entry ops (fun l => labels (.inl l))
      (some (labels (.inr fallback))) = some (labels (planMain ops fallback)) := by
  cases ops <;> rfl

def entry (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Label n ports direction :=
  planMain (commands n ports direction) (.inl ())

def headerPlacement {max : Nat} (placement : PoweringMachineTapes.Tape max → K)
    (output : K) (i : PoweringMachineTapes.Tape max) : K :=
  if i = .inl 10 then output else placement i

omit [DecidableEq K] in
@[simp] theorem headerPlacement_output {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K) :
    headerPlacement placement output (.inl 10) = output := by simp [headerPlacement]

omit [DecidableEq K] in
theorem headerPlacement_other {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K)
    (i : PoweringMachineTapes.Tape max) (hi : i ≠ .inl 10) :
    headerPlacement placement output i = placement i := by simp [headerPlacement, hi]

omit [DecidableEq K] in
theorem headerPlacement_injective {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    Function.Injective (headerPlacement placement output) := by
  intro i j h
  by_cases hi : i = .inl 10
  · subst i
    by_cases hj : j = .inl 10
    · exact hj.symm
    · exact False.elim (outside j (by simpa [headerPlacement, hj] using h))
  · by_cases hj : j = .inl 10
    · subst j
      exact False.elim (outside i (by simpa [headerPlacement, hi] using h.symm))
    · exact distinct (by simpa [headerPlacement, hi, hj] using h)

omit [DecidableEq K] in
theorem headerPlacement_excludes_data {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    ∀ i, placement (.inl 10) ≠ headerPlacement placement output i := by
  intro i h
  by_cases hi : i = .inl 10
  · subst i
    exact outside _ (by simpa only [headerPlacement_output] using h.symm)
  · have heq : (.inl 10 : PoweringMachineTapes.Tape max) = i :=
      distinct (by simpa [headerPlacement, hi] using h)
    exact hi heq.symm

def instruction (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K)
    (output : K) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ) :
    Label n ports direction → TM2.Stmt (fun _ : K => Bool) Λ (State d n)
  | .inl q => PoweringMachinePlan.instruction placement (commands n ports direction)
      (fun z => labels (.inl z)) (some (labels (.inr (.inl ())))) q
  | .inr (.inl _) => PoweringMasterState.rowAt (t := n + 1) (placement (.inl 10)) output
      (PoweringRowData.fixedLabelAt d n) (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n)))))
  | .inr (.inr q) => PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction (fun z => labels (.inr (.inr z))) exit q

def afterPlan (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  PoweringMachinePlan.finalTapes graph placement vertex (commands n ports direction) base

def rowRelation (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Bool :=
  encodeWords (GenericGraphTables.relationWords (PoweringTables.table graph n).rows[
    PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports)].relation)

def rowWords (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Nat :=
  GenericGraphTables.rowWords (PoweringTables.table graph n).rows[
    PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports)]

def afterEmit (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterPlan graph n placement vertex ports direction base
  Function.update (Function.update mid (placement (.inl 10)) []) output
    (rowRelation graph n vertex ports direction ++ mid output)

def finalTapes (graph : PortTables.Table vertices d)
    (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) : K → List Bool :=
  PoweringMachineRowHeaders.finalTapes graph n (by unfold capacity; omega)
    (headerPlacement placement output) vertex ports direction
    (afterEmit graph n placement output vertex ports direction base)

def planSteps {max : Nat} (graph : PortTables.Table vertices d) (vertex : Fin vertices) :
    List (PoweringMachinePlan.Command d max) → Nat
  | [] => 0
  | op :: ops => PoweringMachineField.steps graph vertex op.val + planSteps graph vertex ops

theorem planSteps_eq {max : Nat} (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (ops : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex ops base = planSteps graph vertex ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons op ops ih =>
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex ops
          (PoweringMachinePlan.result graph placement vertex op base) = _
      rw [ih]
      rfl

def steps (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  planSteps graph vertex (commands n ports direction) + 1 +
    PoweringMachineRowHeaders.steps graph n vertex ports direction

def Ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices)
    (suffix : List Bool) (base : K → List Bool) : Prop :=
  PoweringMachineField.Ready graph placement vertex suffix base ∧ base (placement (.inl 10)) = []

private theorem plan_other_inline_PoweringMachineRowBody {max : Nat} (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (ops : List (PoweringMachinePlan.Command d max)) (base : K → List Bool)
    (k : K) (outside : ∀ i, k ≠ placement i) :
    PoweringMachinePlan.finalTapes graph placement vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons op ops ih =>
      change PoweringMachinePlan.finalTapes graph placement vertex ops
        (PoweringMachinePlan.result graph placement vertex op base) k = _
      rw [ih]
      exact PoweringMachineField.finalTapes_other graph placement vertex op.val op.property base k outside

theorem afterEmit_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_self]

theorem afterEmit_role (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (j : Fin 11) (hj : j ≠ 10) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl j)) =
      afterPlan graph n placement vertex ports direction base (placement (.inl j)) := by
  have hdata : placement (.inl j) ≠ placement (.inl 10) := fun h => hj (Sum.inl.inj (distinct h))
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_of_ne hdata]

theorem afterEmit_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (afterEmit graph n placement output vertex ports direction base) := by
  have hp := PoweringMachinePlan.ready_finalTapes graph placement distinct vertex
    (commands n ports direction) base suffix ready.1
  constructor
  · constructor
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 0 (by decide)]
      exact hp.table
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 1 (by decide)]
      exact hp.source
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 5 (by decide)]
      exact hp.scratch
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 8 (by decide)]
      exact hp.leftCopy
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 9 (by decide)]
      exact hp.rightCopy
  · exact afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  have hother := headerPlacement_excludes_data placement distinct output outside
  calc
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hother _) (hother _) (hother _) (hother _) (fun i => hother _)
    _ = [] := afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (finalTapes graph n placement output vertex ports direction base) := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hrole (j : Fin 11) (h₂ : j ≠ 2) (h₃ : j ≠ 3) (h₄ : j ≠ 4) (h₁₀ : j ≠ 10) :
      finalTapes graph n placement output vertex ports direction base (placement (.inl j)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl j)) := by
    have h := PoweringMachineRowHeaders.finalTapes_shared graph n (by unfold capacity; omega)
      (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
      vertex ports direction (afterEmit graph n placement output vertex ports direction base) j h₂ h₃ h₄ h₁₀
    dsimp only [finalTapes]
    simpa only [headerPlacement, ite_eq_right (show (Sum.inl j : PoweringMachineTapes.Tape (capacity n)) ≠ .inl 10 from
      fun heq => h₁₀ (Sum.inl.inj heq))] using h
  constructor
  · constructor
    · rw [hrole 0 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.table
    · rw [hrole 1 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.source
    · rw [hrole 5 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.scratch
    · rw [hrole 8 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.leftCopy
    · rw [hrole 9 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.rightCopy
  · exact finalTapes_data graph n placement distinct output outside vertex ports direction base

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex ports direction base k = base k := by
  have hh : ∀ i, k ≠ headerPlacement placement output i := by
    intro i
    by_cases hi : i = .inl 10
    · simpa [headerPlacement, hi] using hout
    · simpa [headerPlacement, hi] using outside i
  calc
    finalTapes graph n placement output vertex ports direction base k =
        afterEmit graph n placement output vertex ports direction base k :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hh _) (hh _) (hh _) (hh _) (fun i => hh _)
    _ = afterPlan graph n placement vertex ports direction base k := by
      simp only [afterEmit, Function.update_of_ne hout, Function.update_of_ne (outside _)]
    _ = base k := plan_other_inline_PoweringMachineRowBody graph placement vertex _ base k outside

theorem rowBlock_eq_rowRelation (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock
      (PoweringRowData.fixedLabelAt d n) (PoweringRowData.rowBits graph n (direction, vertex, ports)))) =
      rowRelation graph n vertex ports direction := by
  calc
    _ = encodeWords (GenericGraphTables.relationWords
        (PoweringRowData.emittedRelation graph n (direction, vertex, ports))) :=
      PoweringRowData.rowBlock_unary graph n (direction, vertex, ports)
    _ = _ := by
      have h := PoweringRowData.emittedRelation_table graph n
        (PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports))
      rw [PoweringEnumeration.decodeDart_encodeDart] at h
      exact congrArg (fun relation : GenericGraphTables.RelationTable (PoweringTables.labelCount d n) =>
        encodeWords (GenericGraphTables.relationWords relation)) h

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex ports direction base output =
      encodeWords (rowWords graph n vertex ports direction) ++ base output := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction id none
    (PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction id none) (fun _ => rfl)
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source) () none).2
  simp only [PoweringMachineTapes.rowOutput, headerPlacement_output] at hh
  calc
    finalTapes graph n placement output vertex ports direction base output =
        encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
          afterEmit graph n placement output vertex ports direction base output := hh
    _ = encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
        (rowRelation graph n vertex ports direction ++ base output) := by
      simp only [afterEmit, Function.update_self]
      rw [show afterPlan graph n placement vertex ports direction base output = base output from
        plan_other_inline_PoweringMachineRowBody graph placement vertex _ base output outside]
    _ = _ := PoweringRowHeaderSemantics.header_relation_bits graph n vertex ports direction (base output)

theorem rowTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output ports direction labels exit l)
    (base : K → List Bool) (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n ports direction]
      (some ⟨some (labels (entry n ports direction)), PoweringMasterState.clean (bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (bufferSize d n),
        finalTapes graph n placement output vertex ports direction base⟩ := by
  have hp := PoweringMachinePlan.planTrace graph placement distinct vertex (commands n ports direction)
    (fun q => labels (.inl q)) (some (labels (.inr (.inl ())))) program
    (fun q => atLabels (.inl q)) base suffix ready.1 (emptyBuffer (bufferSize d n))
  rw [planSteps_eq, plan_entry_eq] at hp
  let mid := afterPlan graph n placement vertex ports direction base
  have hinput : mid (placement (.inl 10)) = PoweringMachineRow.encodeBits
      (List.ofFn (PoweringRowData.rowBits graph n (direction, vertex, ports))) ++ [] := by
    dsimp only [mid, afterPlan, commands]
    have h := PoweringMachinePlan.rowPlan_output graph n ports direction placement distinct vertex base suffix ready.1
    simpa only [ready.2, List.append_nil, PoweringRowData.dataTape_eq] using h
  have hr := PoweringMasterState.step_rowAt_clean (t := n + 1) (placement (.inl 10)) output
    (PoweringRowData.fixedLabelAt d n)
    (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n))))) program (labels (.inr (.inl ())))
    (atLabels (.inr (.inl ()))) (Ne.symm (outside _))
    (PoweringRowData.rowBits graph n (direction, vertex, ports))
    (emptyBuffer (bufferSize d n)) [] mid hinput
  rw [rowBlock_eq_rowRelation] at hr
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction (fun q => labels (.inr (.inr q))) exit program
    (fun q => atLabels (.inr (.inr q)))
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source)
    (emptyBuffer (bufferSize d n), false, none) none).1
  rw [steps, Nat.add_comm, Function.iterate_add_apply, Function.iterate_succ_apply']
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (advance (TM2.step program) ((advance (TM2.step program))^[planSteps graph vertex (commands n ports direction)]
      (some ⟨some (labels (planMain (commands n ports direction) (.inl ()))),
        MachineUnaryEqualityBit.clean (emptyBuffer (bufferSize d n)), base⟩))) = _
  rw [hp]
  simp only [advance_some]
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (TM2.step program ⟨some (labels (.inr (.inl ()))),
      PoweringMasterState.withBuffer (emptyBuffer (bufferSize d n)), mid⟩) = _
  rw [hr]
  exact hh

def budget (d n inputLength : Nat) : Nat :=
  PoweringPlanBudget.rowBudget d n inputLength + 1 +
    ((14 * (n + 1) + 4) * inputLength + 12 * (n + 1) + 6)

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps graph vertex n ports direction ≤ budget d n (PortTables.tableBits graph).length := by
  have hp := PoweringPlanBudget.rowPlan_steps_le graph n ports direction id vertex (fun _ => [])
  rw [planSteps_eq] at hp
  have hh := PoweringMachineRowHeaders.steps_le graph n vertex ports direction
  change planSteps graph vertex (commands n ports direction) ≤
    PoweringPlanBudget.rowBudget d n (PortTables.tableBits graph).length at hp
  unfold steps budget
  omega

def rowInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output ports direction labels exit l)
    (base : K → List Bool) (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry n ports direction)), PoweringMasterState.clean (bufferSize d n), base⟩
      (some ⟨exit, PoweringMasterState.clean (bufferSize d n),
        finalTapes graph n placement output vertex ports direction base⟩)
      (budget d n (PortTables.tableBits graph).length) where
  steps := steps graph vertex n ports direction
  evals_in_steps := rowTrace graph n placement distinct output outside vertex ports direction
    labels exit program atLabels base suffix ready
  steps_le_m := steps_le graph vertex n ports direction

end DFVSGames.Foundations.Complexity.PoweringMachineRowBody
end

section

namespace DFVSGames.Foundations.PCP.PoweringTableLayout

open DFVSGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

def blockSize (d n : Nat) : Nat := 2 * d ^ (n + 1)

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  unfold dartCount blockSize
  ac_rfl

def blockIndex {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) : Fin (dartCount vertices d n) :=
  Fin.cast (dartCount_eq_vertex_blocks vertices d n).symm
    (finProdFinEquiv (v, j))

@[simp] theorem blockIndex_val {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) :
    (blockIndex d n v j).val = blockSize d n * v.val + j.val := by
  change j.val + blockSize d n * v.val = blockSize d n * v.val + j.val
  exact Nat.add_comm _ _

theorem blockIndex_eq_encodeDart {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) (direction : Bool) :
    blockIndex d n v (dartBlockEquiv d n (p, direction)) =
      encodeDart vertices d n (direction, (v, p)) := by
  apply Fin.ext
  change (dartBlockEquiv d n (p, direction)).val + (2 * d ^ (n + 1)) * v.val =
    (dartEquiv vertices d n (direction, (v, p))).val
  rw [dartEquiv_val, dartBlockEquiv_val]
  omega

def vertexRows {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) :
    List (GenericGraphTables.DartRow (labelCount d n) vertices (dartCount vertices d n)) :=
  List.ofFn (fun j : Fin (blockSize d n) => (table input n).rows[blockIndex d n v j])

def vertexRowWords {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Nat :=
  (vertexRows input n v).flatMap GenericGraphTables.rowWords

def vertexRowBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) : List Bool :=
  encodeWords (vertexRowWords input n v)

@[simp] theorem vertexRows_length {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (v : Fin vertices) :
    (vertexRows input n v).length = blockSize d n := by
  exact List.length_ofFn (f := fun j : Fin (blockSize d n) =>
    (table input n).rows[blockIndex d n v j])

private theorem vector_toList_ofFn_inline_PoweringTableLayout {α : Type*} {m : Nat} (rows : Vector α m) :
    rows.toList = List.ofFn (fun i : Fin m => rows[i]) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

private theorem vector_blocks_inline_PoweringTableLayout {α : Type*} {m vertices width : Nat}
    (sameCount : m = vertices * width) (rows : Vector α m) :
    rows.toList = (List.finRange vertices).flatMap (fun v =>
      List.ofFn (fun j : Fin width =>
        rows[Fin.cast sameCount.symm (finProdFinEquiv (v, j))])) := by
  have atIndex (v : Fin vertices) (j : Fin width)
      (h : v.val * width + j.val < vertices * width) :
      (⟨v.val * width + j.val, h⟩ : Fin (vertices * width)) =
        finProdFinEquiv (v, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [vector_toList_ofFn_inline_PoweringTableLayout rows,
    List.ofFn_congr sameCount (fun i : Fin m => rows[i]), List.ofFn_mul]
  simp only [atIndex, List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem rowList_eq_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.rowList (table input n) =
      (List.finRange vertices).flatMap (vertexRows input n) := by
  exact vector_blocks_inline_PoweringTableLayout (dartCount_eq_vertex_blocks vertices d n) (table input n).rows

theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  apply congrArg ([vertices, dartCount vertices d n] ++ ·)
  exact (congrArg (List.flatMap GenericGraphTables.rowWords)
    (rowList_eq_vertexRows input n)).trans
      (List.flatMap_assoc (l := List.finRange vertices) (f := vertexRows input n)
        (g := GenericGraphTables.rowWords))

private theorem encodeWords_flatMap_inline_PoweringTableLayout {α : Type*} (items : List α)
    (words : α → List Nat) :
    encodeWords (items.flatMap words) =
      items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem outputBits_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    outputBits input n = encodeWords [vertices, dartCount vertices d n] ++
      (List.finRange vertices).flatMap (vertexRowBits input n) := by
  unfold outputBits GenericGraphTables.tableBits
  rw [outputWords_vertexRows, encodeWords_append, encodeWords_flatMap_inline_PoweringTableLayout]
  rfl

theorem vertexRowWords_length {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (vertexRowWords input n v).length =
      (labelCount d n * labelCount d n + 2) * blockSize d n := by
  unfold vertexRowWords
  rw [GenericGraphTables.rowsWords_length, vertexRows_length]

theorem vertexRowBits_length_ge {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (labelCount d n * labelCount d n + 2) * blockSize d n ≤
      (vertexRowBits input n v).length := by
  unfold vertexRowBits
  rw [encodeWords_length, vertexRowWords_length]
  omega

theorem vertexRowBits_length_le {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (v : Fin vertices) :
    (vertexRowBits input n v).length ≤
      blockSize d n *
        (vertices + dartCount vertices d n + 2 * (labelCount d n * labelCount d n)) := by
  have h := GenericGraphTables.rowsBits_length_le (vertexRows input n v)
  rw [vertexRows_length] at h
  exact h

theorem outputHeader_length (vertices d n : Nat) :
    (encodeWords [vertices, dartCount vertices d n]).length =
      vertices + dartCount vertices d n + 2 := by
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Foundations.PCP.PoweringTableLayout
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Command (d n : Nat) := Fin (PoweringTableLayout.blockSize d n)

def ports {d n : Nat} (j : Command d n) : Fin (n + 1) → Fin d :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).1

def direction {d n : Nat} (j : Command d n) : Bool :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).2

def commands (d n : Nat) : List (Command d n) := (List.ofFn id).reverse

@[simp] theorem commands_length (d n : Nat) :
    (commands d n).length = PoweringTableLayout.blockSize d n := by
  simp only [commands, List.length_reverse, List.length_ofFn]

abbrev LocalLabel (j : Command d n) := PoweringMachineRowBody.Label n (ports j) (direction j)
abbrev SequenceLabel (ops : List (Command d n)) := MachineFiniteSequence.Label LocalLabel ops
abbrev Label (d n : Nat) := SequenceLabel (commands d n)
abbrev State (d n : Nat) := PoweringMachineRowBody.State d n

def sequenceEntry (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j)) ops labels exit

def entry (d n : Nat) (labels : Label d n → Λ) (exit : Option Λ) : Option Λ :=
  sequenceEntry (commands d n) labels exit

def sequenceInstruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : SequenceLabel ops → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  MachineFiniteSequence.instruction LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    ops labels exit

def instruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (labels : Label d n → Λ) (exit : Option Λ) :
    Label d n → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  sequenceInstruction n placement output (commands d n) labels exit

def result (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (j : Command d n) (base : K → List Bool) :
    K → List Bool :=
  PoweringMachineRowBody.finalTapes graph n placement output vertex (ports j) (direction j) base

def sequenceTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    K → List Bool :=
  MachineFiniteSequence.resultOf (result graph n placement output vertex) ops base

def finalTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool) : K → List Bool :=
  sequenceTapes graph n placement output vertex (commands d n) base

def sequenceSteps (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j)) ops base

def costSum (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    List (Command d n) → Nat
  | [] => 0
  | j :: ops => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
      costSum graph vertex n ops

theorem sequenceSteps_eq (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    sequenceSteps graph n placement output vertex ops base = costSum graph vertex n ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        sequenceSteps graph n placement output vertex ops
          (result graph n placement output vertex j base) = _
      rw [ih]
      rfl

def steps (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) : Nat :=
  costSum graph vertex n (commands d n)

def budget (d n inputLength : Nat) : Nat :=
  PoweringTableLayout.blockSize d n * PoweringMachineRowBody.budget d n inputLength

theorem costSum_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ops : List (Command d n)) :
    costSum graph vertex n ops ≤
      ops.length * PoweringMachineRowBody.budget d n (PortTables.tableBits graph).length := by
  induction ops with
  | nil => simp only [costSum, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons j ops ih =>
      have hfirst := PoweringMachineRowBody.steps_le graph vertex n (ports j) (direction j)
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        costSum graph vertex n ops ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add hfirst ih

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    steps graph vertex n ≤ budget d n (PortTables.tableBits graph).length := by
  simpa only [steps, budget, commands_length] using costSum_le graph vertex n (commands d n)

theorem sequenceTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n))
    (labels : SequenceLabel ops → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction n placement output ops labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[sequenceSteps graph n placement output vertex ops base]
      (some ⟨sequenceEntry ops labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        sequenceTapes graph n placement output vertex ops base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j))
    program (PoweringMachineRowBody.Ready graph n placement vertex suffix)
    (fun _ => PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)) id ops
  · intro j _ tapes good
    exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
      vertex (ports j) (direction j) tapes suffix good
  · intro j _ localLabels localExit atLocal tapes good
    exact PoweringMachineRowBody.rowTrace graph n placement distinct output outside vertex
      (ports j) (direction j) localLabels localExit program atLocal tapes suffix good
  · exact atLabels
  · exact ready

theorem vertexTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n]
      (some ⟨entry d n labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩ := by
  have h := sequenceTrace graph n placement distinct output outside vertex (commands d n)
    labels exit program atLabels base suffix ready
  rw [sequenceSteps_eq] at h
  exact h

theorem sequenceTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (sequenceTapes graph n placement output vertex ops base) := by
  induction ops generalizing base with
  | nil => exact ready
  | cons j ops ih =>
      apply ih
      exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
        vertex (ports j) (direction j) base suffix ready

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (finalTapes graph n placement output vertex base) :=
  sequenceTapes_ready graph n placement distinct output outside vertex (commands d n) base suffix ready

theorem sequenceTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    sequenceTapes graph n placement output vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) k = _
      rw [ih]
      exact PoweringMachineRowBody.finalTapes_other graph n placement output vertex
        (ports j) (direction j) base k hout outside

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex base k = base k :=
  sequenceTapes_other graph n placement output vertex (commands d n) base k hout outside

def rowBits (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) : List Bool :=
  encodeWords (PoweringMachineRowBody.rowWords graph n vertex (ports j) (direction j))

theorem blockIndex_eq_encodeDart (n : Nat) (vertex : Fin vertices) (j : Command d n) :
    PoweringTableLayout.blockIndex d n vertex j =
      PoweringEnumeration.encodeDart vertices d n (direction j, vertex, ports j) := by
  exact (congrArg (PoweringTableLayout.blockIndex d n vertex)
    ((PoweringEnumeration.dartBlockEquiv d n).apply_symm_apply j)).symm.trans
      (PoweringTableLayout.blockIndex_eq_encodeDart d n vertex (ports j) (direction j))

theorem rowBits_eq (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (j : Command d n) :
    rowBits graph n vertex j = encodeWords (GenericGraphTables.rowWords
      (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
  rw [blockIndex_eq_encodeDart]
  rfl

private theorem encodeWords_flatMap_inline_PoweringMachineVertex {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem rows_eq_vertexRowBits (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) :
    (List.ofFn id : List (Command d n)).flatMap (rowBits graph n vertex) =
      PoweringTableLayout.vertexRowBits graph n vertex := by
  have hrows : (List.ofFn id : List (Command d n)).map
      (fun j => (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) =
      List.ofFn (fun j : Command d n =>
        (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j]) := by
    simp only [List.map_ofFn, Function.comp_id]
  calc
    _ = (List.ofFn id : List (Command d n)).flatMap (fun j => encodeWords
        (GenericGraphTables.rowWords
          (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j])) := by
      apply congrArg (List.flatMap · (List.ofFn id))
      funext j
      exact rowBits_eq graph n vertex j
    _ = PoweringTableLayout.vertexRowBits graph n vertex := by
      exact (List.flatMap_map
        (fun j : Command d n =>
          (PoweringTables.table graph n).rows[PoweringTableLayout.blockIndex d n vertex j])
        (fun row => encodeWords (GenericGraphTables.rowWords row)) (List.ofFn id)).symm.trans
          ((congrArg (List.flatMap (fun row => encodeWords (GenericGraphTables.rowWords row)))
            hrows).trans
              (encodeWords_flatMap_inline_PoweringMachineVertex
                (PoweringTableLayout.vertexRows graph n vertex) GenericGraphTables.rowWords).symm)

theorem sequenceTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    sequenceTapes graph n placement output vertex ops base output =
      ops.reverse.flatMap (rowBits graph n vertex) ++ base output := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      have nextReady := PoweringMachineRowBody.finalTapes_ready graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) output = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineRowBody.finalTapes_output graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, rowBits]

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex base output =
      PoweringTableLayout.vertexRowBits graph n vertex ++ base output := by
  rw [finalTapes, sequenceTapes_output graph n placement distinct output outside vertex
    (commands d n) base suffix ready]
  simp only [commands, List.reverse_reverse, rows_eq_vertexRowBits]

def vertexInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry d n labels exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩
      (some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩)
      (budget d n (PortTables.tableBits graph).length) where
  steps := steps graph vertex n
  evals_in_steps := vertexTrace graph n placement distinct output outside vertex labels exit
    program atLabels base suffix ready
  steps_le_m := steps_le graph vertex n

end DFVSGames.Foundations.Complexity.PoweringMachineVertex
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
