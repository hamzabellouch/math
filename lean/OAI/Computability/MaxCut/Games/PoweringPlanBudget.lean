import Mathlib
import OAI.Computability.MaxCut.Machines.PoweringMachineField

namespace OAI

/-!
# Execution budget of the concrete powered-row field plan

The cost is the sum of the actual relation and endpoint-comparison transition
counts. Each fixed command scans only the serialized input graph. The execution
certificates below instantiate the concrete plan trace; no execution witness or
running-time bound is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

/-- A common bound for either concrete field operation of radius at most `max`. -/
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

/-- Sum the actual recursive cost, including its changing intermediate tapes. -/
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

/-- This is the actual static instruction list's length, not a supplied bound. -/
@[simp] theorem boundedRowPlan_length (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringMachinePlan.boundedRowPlan n ports direction).length =
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) := by
  simp only [PoweringMachinePlan.boundedRowPlan, List.length_ofFn]

/-- For fixed degree and radius this is affine in the serialized graph length. -/
def rowBudget (d n inputLength : Nat) : Nat :=
  PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
    fieldBudget (2 * (n + 1)) inputLength

/-- The backwards plan that produces the actual row-data tape obeys this bound. -/
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

/-- A genuine execution certificate for an arbitrary concrete bounded plan. -/
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

/-- The actual row-data plan runs within the explicit fixed-plan affine bound. -/
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

end MaxCutGames.Foundations.Complexity.PoweringPlanBudget

end OAI
