import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.PoweringGlobalEnumerationLemmas
import OAI.Computability.UniqueGames.Machines.PoweringMachineFinish
import OAI.Computability.UniqueGames.Machines.PoweringMachineVertex

namespace OAI

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K
abbrev State := PoweringMachineVertex.State

structure Ready (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (base : K → List Bool) : Prop where
  table : base (placement (.inl 0)) = PortTables.tableBits graph
  scratch : base (placement (.inl 5)) = []
  leftCopy : base (placement (.inl 8)) = []
  rightCopy : base (placement (.inl 9)) = []
  data : base (placement (.inl 10)) = []

def counter (placement : Placement K n) (base : K → List Bool) (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

theorem counter_other (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

theorem ready_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (ready : Ready graph n placement base) (vertex : Fin vertices) :
    PoweringMachineRowBody.Ready graph n placement vertex [] (counter placement base vertex.val) := by
  constructor
  · constructor
    · rw [counter_other placement distinct base vertex.val 0 (by decide)]
      exact ready.table
    · simp only [counter, MachineUnaryCounter.counterTapes_counter]
    · rw [counter_other placement distinct base vertex.val 5 (by decide)]
      exact ready.scratch
    · rw [counter_other placement distinct base vertex.val 8 (by decide)]
      exact ready.leftCopy
    · rw [counter_other placement distinct base vertex.val 9 (by decide)]
      exact ready.rightCopy
  · rw [counter_other placement distinct base vertex.val 10 (by decide)]
    exact ready.data

omit [DecidableEq K] in
theorem ready_of_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (base : K → List Bool) (vertex : Fin vertices)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex [] base) :
    Ready graph n placement base :=
  ⟨ready.1.table, ready.1.scratch, ready.1.leftCopy, ready.1.rightCopy, ready.2⟩

def vertexStart (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) : Λ :=
  (PoweringMachineVertex.entry d n labels (some guardLabel)).getD guardLabel

theorem vertexEntry (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    PoweringMachineVertex.entry d n labels (some guardLabel) =
      some (vertexStart d n labels guardLabel) := by
  unfold vertexStart PoweringMachineVertex.entry PoweringMachineVertex.sequenceEntry
  have h : ∀ (commands : List (PoweringMachineVertex.Command d n))
      (labels : MachineFiniteSequence.Label PoweringMachineVertex.LocalLabel commands → Λ),
      MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel) =
      some ((MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel)).getD guardLabel) := by
    intro commands labels
    cases commands <;> rfl
  exact h _ labels

def bridge (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  .goto (fun _ => vertexStart d n labels guardLabel)

/-- The exact tapes produced by repeatedly executing the actual vertex body. -/
def finalTapes (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (output : K) : (remaining : Nat) → remaining ≤ vertices → (K → List Bool) → K → List Bool
  | 0, _, base => counter placement base 0
  | r + 1, bounded, base =>
      finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output ⟨r, by omega⟩
          (counter placement base r))

def steps (graph : PortTables.Table vertices d) (n : Nat) :
    (remaining : Nat) → remaining ≤ vertices → Nat
  | 0, _ => 1
  | r + 1, bounded =>
      2 + PoweringMachineVertex.steps graph ⟨r, by omega⟩ n + steps graph n r (by omega)

theorem steps_le (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    steps graph n remaining bounded ≤
      remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1 := by
  induction remaining with
  | zero => simp [steps]
  | succ r ih =>
      have hv := PoweringMachineVertex.steps_le graph (⟨r, by omega⟩ : Fin vertices) n
      have hi := ih (by omega)
      simp only [steps, Nat.add_mul, Nat.one_mul]
      omega

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    Ready graph n placement (finalTapes graph n placement output remaining bounded base) := by
  induction remaining generalizing base with
  | zero =>
      constructor
      · rw [finalTapes, counter_other placement distinct base 0 0 (by decide)]
        exact ready.table
      · rw [finalTapes, counter_other placement distinct base 0 5 (by decide)]
        exact ready.scratch
      · rw [finalTapes, counter_other placement distinct base 0 8 (by decide)]
        exact ready.leftCopy
      · rw [finalTapes, counter_other placement distinct base 0 9 (by decide)]
        exact ready.rightCopy
      · rw [finalTapes, counter_other placement distinct base 0 10 (by decide)]
        exact ready.data
  | succ r ih =>
      apply ih
      apply ready_of_vertex graph n placement _ (⟨r, by omega⟩ : Fin vertices)
      exact PoweringMachineVertex.finalTapes_ready graph n placement distinct output outside
        ⟨r, by omega⟩ _ [] (ready_vertex graph n placement distinct base ready _)

def prefixRows (graph : PortTables.Table vertices d) (n : Nat) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixRows graph n r ++
      if h : r < vertices then PoweringTableLayout.vertexRowBits graph n ⟨r, h⟩ else []

theorem prefixRows_ofFn (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    prefixRows graph n remaining =
      (List.ofFn (fun i : Fin remaining =>
        PoweringTableLayout.vertexRowBits graph n (Fin.castLE bounded i))).flatten := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      have hr : r < vertices := by omega
      rw [prefixRows, dite_eq_left hr, List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      change prefixRows graph n r ++ PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩ =
        (List.ofFn (fun i : Fin r => PoweringTableLayout.vertexRowBits graph n
          (Fin.castLE (show r ≤ vertices by omega) i))).flatten ++
          PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩
      rw [ih]

theorem prefixRows_all (graph : PortTables.Table vertices d) (n : Nat) :
    prefixRows graph n vertices =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [prefixRows_ofFn graph n vertices (Nat.le_refl _)]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    finalTapes graph n placement output remaining bounded base output =
      prefixRows graph n remaining ++ base output := by
  induction remaining generalizing base with
  | zero =>
      exact MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _)
        base 0 []
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      have vertexReady := ready_vertex graph n placement distinct base ready vertex
      have nextReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      change finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output vertex current) output = _
      rw [ih (by omega) _ (ready_of_vertex graph n placement _ vertex nextReady),
        PoweringMachineVertex.finalTapes_output graph n placement distinct output outside
          vertex current [] vertexReady]
      have hc : current output = base output :=
        MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _) base r []
      rw [hc, prefixRows, dite_eq_left vertex.isLt, List.append_assoc]

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (output : K) (remaining : Nat)
    (bounded : remaining ≤ vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output remaining bounded base k = base k := by
  induction remaining generalizing base with
  | zero => exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base 0 []
  | succ r ih =>
      rw [finalTapes, ih, PoweringMachineVertex.finalTapes_other graph n placement output
        ⟨r, by omega⟩ _ k hout outside]
      exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base r []

theorem loopTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    (advance (TM2.step program))^[steps graph n remaining bounded]
      (some ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩) =
      some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩ := by
  let initial := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  induction remaining generalizing base with
  | zero =>
      simpa only [steps, finalTapes, counter, initial, PoweringMasterState.clean,
        PoweringMasterState.withBuffer] using
        MachineUnaryCounter.guardTrace_zero (placement (.inl 1)) guardLabel bridgeLabel exitLabel
          program atGuard base [] initial.1 none
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      let next := PoweringMachineVertex.finalTapes graph n placement output vertex current
      have vertexReady : PoweringMachineRowBody.Ready graph n placement vertex [] current :=
        ready_vertex graph n placement distinct base ready vertex
      have nextVertexReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      have nextReady : Ready graph n placement next :=
        ready_of_vertex graph n placement next vertex nextVertexReady
      have sameCounter : counter placement next r = next := by
        have hs := nextVertexReady.1.source
        change next (placement (.inl 1)) = encodeWord r ++ [] at hs
        unfold counter MachineUnaryCounter.counterTapes
        rw [← hs]
        exact Function.update_eq_self _ _
      have tailRun := ih (by omega) next nextReady
      rw [sameCounter] at tailRun
      have guardRun : advance (TM2.step program)
          (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) =
          some ⟨some bridgeLabel, initial, current⟩ := by
        simpa only [advance_some, current, counter, initial, PoweringMasterState.clean,
          PoweringMasterState.withBuffer] using
          MachineUnaryCounter.guardStep_succ (placement (.inl 1)) guardLabel bridgeLabel exitLabel
            program atGuard base r [] initial.1 none
      have bridgeRun : advance (TM2.step program)
          (some ⟨some bridgeLabel, initial, current⟩) =
          some ⟨PoweringMachineVertex.entry d n labels (some guardLabel), initial, current⟩ := by
        change some (TM2.stepAux (program bridgeLabel) initial current) = _
        rw [atBridge, vertexEntry]
        rfl
      have vertexRun := PoweringMachineVertex.vertexTrace graph n placement distinct output outside
        vertex labels (some guardLabel) program atVertex current [] vertexReady
      change (advance (TM2.step program))^[2 + PoweringMachineVertex.steps graph vertex n +
          steps graph n r (by omega)]
        (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) = _
      rw [show 2 + PoweringMachineVertex.steps graph vertex n + steps graph n r (by omega) =
          (steps graph n r (by omega) + PoweringMachineVertex.steps graph vertex n) + 1 + 1 by omega,
        Function.iterate_succ_apply, guardRun, Function.iterate_succ_apply, bridgeRun,
        Function.iterate_add_apply, vertexRun]
      exact tailRun

def loopInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩
      (some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩)
      (remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1) where
  steps := steps graph n remaining bounded
  evals_in_steps := loopTrace graph n placement distinct output outside guardLabel bridgeLabel
    exitLabel labels program atGuard atBridge atVertex remaining bounded base ready
  steps_le_m := steps_le graph n remaining bounded

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineOuterLoop

/-!
# The fixed global powering machine

For fixed degree `d` and radius parameter `n`, this is one concrete finite
machine: initialization, unary vertex guard, the fixed vertex-row producer,
and output-header/cleanup instructions are connected by explicit labels.
Its definition takes no input graph, vertex count, or program callback.

The code equations below expose each actual branch for the separate runtime
proof. The variable-size input graph and counters reside on physical tapes.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

abbrev State (d n : Nat) :=
  PoweringMasterState.Master (PoweringMachineRowBody.bufferSize d n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

abbrev FinishLabel (n : Nat) := PoweringMachineFinish.Label (enumeration n) (outputTape n)

abbrev Label (d n : Nat) := PoweringMachineInitialize.Label ⊕
  (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def initLabels (d n : Nat) : PoweringMachineInitialize.Label → Label d n := Sum.inl
def guardLabel (d n : Nat) : Label d n := .inr (.inl false)
def bridgeLabel (d n : Nat) : Label d n := .inr (.inl true)

def vertexLabels (d n : Nat) (label : PoweringMachineVertex.Label d n) : Label d n :=
  .inr (.inr (.inl label))

def finishLabels (d n : Nat) (label : FinishLabel n) : Label d n :=
  .inr (.inr (.inr label))

/-- Finish first copies the dart-count field, then the vertex-count field. -/
def finishEntry (d n : Nat) : Label d n := finishLabels d n (.inl .seed)

/-- Initialization first clones the input's live vertex-count field. -/
def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

/-- The complete program, fixed solely by the reduction parameters. -/
def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

/-- All state and control spaces are explicit finite types; only the tapes
hold variable-size data. -/
def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

theorem input_ne_output (n : Nat) : inputTape n ≠ outputTape n :=
  PoweringMachineInitialize.commonPlacement_ne_finalOutput (PoweringMachineRowBody.capacity n)
    (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal

/-!
# Concrete global configurations and tape separation

These lemmas specialize the checked initializer placement to the fixed global
machine. The final configuration is the actual `Turing.haltList`, with the
machine's clean initial register and only the output tape populated.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration

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
  simp only [machine]
  rfl

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

end UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration

end OAI
