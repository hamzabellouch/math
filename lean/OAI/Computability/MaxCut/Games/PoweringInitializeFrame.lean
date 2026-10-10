import Mathlib
import OAI.Computability.MaxCut.Machines.PoweringMachineGlobal

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringInitializeFrame

open Turing PCP

variable {vertices d : Nat}

/-- The extra tapes initially contain only the live serialized table. -/
def initialExtra (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n) → List Bool :=
  fun tape => if tape = .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))
    then PortTables.tableBits graph else []

@[simp] theorem initialExtra_table (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n (.inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) =
      PortTables.tableBits graph := by simp [initialExtra]

theorem initialExtra_other (graph : PortTables.Table vertices d) (n : Nat)
    (tape : PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n))
    (hne : tape ≠ .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) :
    initialExtra graph n tape = [] := by simp [initialExtra, hne]

@[simp] theorem initialExtra_scratch (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n
      (.inl (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n))) = [] := by
  simp [initialExtra, PoweringMachineTapes.table, PoweringMachineTapes.scratch]

/-- Exact frame left by initialization, including the preserved input table. -/
def preparedTapes (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineGlobal.Tape n → List Bool :=
  PoweringMachineInitialize.mergeTapes
    (PoweringMachineLoop.finalTapes (PoweringTableLayout.blockSize d n) vertices [])
    (initialExtra graph n)

theorem prepared_commonRole (graph : PortTables.Table vertices d) (n : Nat)
    (j : Fin 11) (hne : j ≠ 1) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl j)) =
      if j = 0 then PortTables.tableBits graph else [] := by
  simp [preparedTapes, PoweringMachineGlobal.placement,
    PoweringMachineInitialize.commonPlacement, PoweringMachineTapes.start,
    PoweringMachineInitialize.mergeTapes, initialExtra, PoweringMachineTapes.table, hne]

theorem prepared_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) := by
  constructor
  · simpa using prepared_commonRole graph n 0 (by decide)
  · simpa using prepared_commonRole graph n 5 (by decide)
  · simpa using prepared_commonRole graph n 8 (by decide)
  · simpa using prepared_commonRole graph n 9 (by decide)
  · simpa using prepared_commonRole graph n 10 (by decide)

@[simp] theorem prepared_start (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl 1)) =
      encodeWord vertices := by
  simpa only [preparedTapes, PoweringMachineGlobal.placement, PoweringMachineTapes.start] using
    PoweringMachineInitialize.final_counter (PoweringMachineRowBody.capacity n)
      (PoweringTableLayout.blockSize d n) vertices (initialExtra graph n)

/-- Installing the outer-loop counter changes nothing: it is already present. -/
theorem prepared_counter (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.counter (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) vertices = preparedTapes graph n := by
  unfold PoweringMachineOuterLoop.counter MachineUnaryCounter.counterTapes
  rw [List.append_nil, ← prepared_start graph n]
  simp only [Function.update_eq_self]

@[simp] theorem prepared_output (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.outputTape n) = [] := by
  simp [preparedTapes, PoweringMachineGlobal.outputTape, PoweringMachineInitialize.finalOutput,
    PoweringMachineInitialize.mergeTapes, initialExtra]

@[simp] theorem prepared_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerVertices n) = encodeWord vertices := rfl

@[simp] theorem prepared_darts (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := rfl

@[simp] theorem prepared_source (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (.inl PoweringMachineLoop.HeaderTape.source) = [] := rfl

def preparedCfg (graph : PortTables.Table vertices d) (n : Nat) :
    (PoweringMachineGlobal.machine d n).Cfg :=
  ⟨some (PoweringMachineGlobal.guardLabel d n),
    PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), preparedTapes graph n⟩

/-- A homogeneous Boolean description of the machine's literal initial stacks. -/
theorem initialGlobalTapes_eq (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n) =
      fun tape => if tape = PoweringMachineGlobal.inputTape n
        then PortTables.tableBits graph else [] := by
  funext tape
  cases tape with
  | inl field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table]
  | inr field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table, initialExtra]

private theorem machine_initialStacks_inline_PoweringInitializeFrame (d n : Nat) (input : List Bool) :
    (initList (PoweringMachineGlobal.machine d n) input).stk =
      fun tape => if tape = PoweringMachineGlobal.inputTape n then input else [] := by
  funext tape
  by_cases h : tape = PoweringMachineGlobal.inputTape n
  · subst tape
    simp [initList, PoweringMachineGlobal.machine]
    rfl
  · simp only [initList, PoweringMachineGlobal.machine]
    erw [dite_eq_right h, ite_eq_right h]

/-- The trace starts at `Turing.initList`, with no assumed prepared work tapes. -/
theorem initList_eq (graph : PortTables.Table vertices d) (n : Nat) :
    initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph) =
      ⟨some (PoweringMachineGlobal.main d n),
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n)⟩ := by
  have ht := (machine_initialStacks_inline_PoweringInitializeFrame d n (PortTables.tableBits graph)).trans
    (initialGlobalTapes_eq graph n).symm
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- The first serialized input field is the actual number of vertices. -/
theorem tableBits_head (graph : PortTables.Table vertices d) :
    PortTables.tableBits graph = encodeWord vertices ++
      encodeWords (PortTables.tableWords graph).tail := rfl

/-- Initialization of the actual global program from its literal input list.
Every work-tape readiness property follows from the explicit final frame. -/
def initializeInTime (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d n).step
      (initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph))
      (some (preparedCfg graph n)) (3 * vertices + 5) := by
  rw [initList_eq]
  exact PoweringMachineInitialize.initializeAtInTime
    (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
    (PoweringTableLayout.blockSize d n) vertices
    (PoweringMachineGlobal.initLabels d n) (some (PoweringMachineGlobal.guardLabel d n))
    (PoweringMachineGlobal.program d n) (PoweringMachineGlobal.atInit d n)
    (initialExtra graph n) (encodeWords (PortTables.tableWords graph).tail)
    (by rw [initialExtra_table, tableBits_head]) (initialExtra_scratch graph n)
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n))

end MaxCutGames.Foundations.Complexity.PoweringInitializeFrame

/-!
# Concrete global configurations and tape separation

These lemmas specialize the checked initializer placement to the fixed global
machine. The final configuration is the actual `Turing.haltList`, with the
machine's clean initial register and only the output tape populated.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem placement_injective (n : Nat) : Function.Injective (placement n) :=
  PoweringMachineInitialize.commonPlacement_injective (PoweringMachineRowBody.capacity n)

theorem placement_ne_output (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ outputTape n :=
  PoweringMachineInitialize.commonPlacement_ne_finalOutput
    (PoweringMachineRowBody.capacity n) tape

theorem output_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    outputTape n ≠ placement n tape := Ne.symm (placement_ne_output n tape)

theorem headerVertices_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerVertices n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .vertices (by decide))

theorem headerDarts_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerDarts n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .darts (by decide))

theorem placement_ne_headerVertices (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ headerVertices n := Ne.symm (headerVertices_ne_placement n tape)

theorem placement_ne_headerDarts (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    placement n tape ≠ headerDarts n := Ne.symm (headerDarts_ne_placement n tape)

theorem headerVertices_ne_headerDarts (n : Nat) : headerVertices n ≠ headerDarts n := by
  simp [headerVertices, headerDarts]

theorem headerVertices_ne_output (n : Nat) : headerVertices n ≠ outputTape n := by
  simp [headerVertices, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerDarts_ne_output (n : Nat) : headerDarts n ≠ outputTape n := by
  simp [headerDarts, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerVertices_ne_scratch (n : Nat) :
    headerVertices n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerVertices_ne_placement n _

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

theorem scratch_ne_output (n : Nat) :
    placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) ≠
      outputTape n :=
  placement_ne_output n _

/-- A Boolean tape alphabet is constant, so the type-equality transport in
the bundled machine's dependent stack specification leaves its word intact. -/
@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

/-- The dependent stack definition in `haltList` is exactly the Boolean output
tape shape produced by the checked finite cleanup program. -/
theorem haltList_tapes (d n : Nat) (output : List Bool) :
    (Turing.haltList (machine d n) output).stk =
      MachineDrainMany.haltTapes (outputTape n) output := by
  funext tape
  simp only [Turing.haltList, machine, MachineDrainMany.haltTapes]
  by_cases h : tape = outputTape n
  · erw [dite_eq_left h, ite_eq_left h]
    rfl
  · erw [dite_eq_right h, ite_eq_right h]

/-- Exact identity with the global machine's actual output specification. -/
theorem haltList_eq (d n : Nat) (output : List Bool) :
    Turing.haltList (machine d n) output =
      (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        MachineDrainMany.haltTapes (outputTape n) output⟩ : (machine d n).Cfg) := by
  change (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      (Turing.haltList (machine d n) output).stk⟩ : (machine d n).Cfg) = _
  exact congrArg
    (fun tapes => (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      tapes⟩ : (machine d n).Cfg)) (haltList_tapes d n output)

end MaxCutGames.Foundations.Complexity.PoweringGlobalConfiguration

end OAI
