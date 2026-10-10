import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.Row
import OAI.Combinatorics.IndependentSets.Expansion.PoweringPlanBudget
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineRowHeaders

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} {vertices d : Nat}

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

@[simp] theorem headerPlacement_output {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K) :
    headerPlacement placement output (.inl 10) = output := by simp [headerPlacement]

theorem headerPlacement_other {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K)
    (i : PoweringMachineTapes.Tape max) (hi : i ≠ .inl 10) :
    headerPlacement placement output i = placement i := by simp [headerPlacement, hi]

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

variable [DecidableEq K]

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

private theorem plan_other {max : Nat} (graph : PortTables.Table vertices d)
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
    _ = base k := plan_other graph placement vertex _ base k outside

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
        plan_other graph placement vertex _ base output outside]
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

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
