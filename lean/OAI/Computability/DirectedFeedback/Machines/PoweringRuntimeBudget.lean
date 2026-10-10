import Mathlib
import OAI.Computability.DirectedFeedback.Machines.PoweringMachineOuterLoop

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

namespace DFVSGames.Foundations.Complexity.PoweringRuntimeBudget

open Turing

theorem stackLength_le_of_execution (tm : FinTM2) (start finish : tm.Cfg)
    (initialBound priorBudget : Nat)
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (prior : StateTransition.EvalsToInTime tm.step start (some finish) priorBudget)
    (k : tm.K) :
    (finish.stk k).length ≤ initialBound + priorBudget * Runtime.programPushBound tm := by
  have grown := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) prior
  exact grown.trans (Nat.add_le_add_right (initial k) _)

theorem stackLength_le_from_input (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (finish : tm.Cfg) (priorBudget : Nat)
    (prior : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some finish) priorBudget) (k : tm.K) :
    (finish.stk k).length ≤ input.length + priorBudget * Runtime.programPushBound tm :=
  stackLength_le_of_execution tm (initList tm input) finish input.length priorBudget
    (Runtime.initialStackLength tm input) prior k

abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

theorem finish_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3) := by
  exact PoweringMachineFinish.steps_le_uniform (PoweringMachineGlobal.enumeration radius)
    (PoweringMachineGlobal.outputTape radius) before.stk vertices darts
    (input.length + priorBudget * Runtime.programPushBound (PoweringMachineGlobal.machine d radius))
    (stackLength_le_from_input (PoweringMachineGlobal.machine d radius) input before priorBudget prior)

theorem total_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    prior.steps + PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      priorBudget + (2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3)) :=
  Nat.add_le_add prior.steps_le_m
    (finish_steps_le_of_execution d radius input before priorBudget vertices darts prior)

end DFVSGames.Foundations.Complexity.PoweringRuntimeBudget
end

section

namespace DFVSGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

def preBudget (d n vertices inputLength : Nat) : Nat :=
  (3 * vertices + 5) +
    (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)

def finishBudget (d n pushBound tapeCount vertices inputLength prior : Nat) : Nat :=
  2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
    tapeCount * (inputLength + prior * pushBound + vertices +
      PoweringTableLayout.blockSize d n * vertices + 3)

def totalBudget (d n pushBound tapeCount vertices inputLength : Nat) : Nat :=
  preBudget d n vertices inputLength +
    finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)

theorem preBudget_mono_vertices (d n inputLength : Nat) {v w : Nat} (h : v ≤ w) :
    preBudget d n v inputLength ≤ preBudget d n w inputLength := by
  have hthree := Nat.mul_le_mul_left 3 h
  have hloop := Nat.mul_le_mul_right (PoweringMachineVertex.budget d n inputLength + 2) h
  unfold preBudget
  omega

theorem finishBudget_mono (d n pushBound tapeCount inputLength : Nat)
    {v w prior later : Nat} (hvertices : v ≤ w) (hprior : prior ≤ later) :
    finishBudget d n pushBound tapeCount v inputLength prior ≤
      finishBudget d n pushBound tapeCount w inputLength later := by
  have hdarts := Nat.mul_le_mul_left (PoweringTableLayout.blockSize d n) hvertices
  have hheader := Nat.mul_le_mul_left 2 (Nat.add_le_add hvertices hdarts)
  have hgrowth := Nat.mul_le_mul_right pushBound hprior
  have hinside : inputLength + prior * pushBound + v +
      PoweringTableLayout.blockSize d n * v + 3 ≤
      inputLength + later * pushBound + w + PoweringTableLayout.blockSize d n * w + 3 := by
    omega
  have hclear := Nat.mul_le_mul_left tapeCount hinside
  unfold finishBudget
  omega

theorem totalBudget_mono_vertices (d n pushBound tapeCount inputLength : Nat)
    {v w : Nat} (hvertices : v ≤ w) :
    totalBudget d n pushBound tapeCount v inputLength ≤
      totalBudget d n pushBound tapeCount w inputLength := by
  have hpre := preBudget_mono_vertices d n inputLength hvertices
  unfold totalBudget
  exact Nat.add_le_add hpre
    (finishBudget_mono d n pushBound tapeCount inputLength hvertices hpre)

noncomputable def rowTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringMachineRowBody.bufferSize d n) *
      (Polynomial.C (28 * (2 * (n + 1)) + 10) * Polynomial.X +
        Polynomial.C (24 * (2 * (n + 1)) + 15)) + Polynomial.C 1 +
    (Polynomial.C (14 * (n + 1) + 4) * Polynomial.X +
      Polynomial.C (12 * (n + 1)) + Polynomial.C 6)

@[simp] theorem rowTime_eval (d n inputLength : Nat) :
    (rowTime d n).eval inputLength = PoweringMachineRowBody.budget d n inputLength := by
  simp only [rowTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PoweringMachineRowBody.budget, PoweringPlanBudget.rowBudget,
    PoweringPlanBudget.fieldBudget, PoweringMachineRowBody.bufferSize, Nat.add_assoc]

noncomputable def vertexTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringTableLayout.blockSize d n) * rowTime d n

@[simp] theorem vertexTime_eval (d n inputLength : Nat) :
    (vertexTime d n).eval inputLength = PoweringMachineVertex.budget d n inputLength := by
  simp only [vertexTime, Polynomial.eval_mul, Polynomial.eval_C, rowTime_eval,
    PoweringMachineVertex.budget]

noncomputable def preTime (d n : Nat) : Polynomial Nat :=
  (Polynomial.C 3 * Polynomial.X + Polynomial.C 5) +
    (Polynomial.X * (vertexTime d n + Polynomial.C 2) + Polynomial.C 1)

@[simp] theorem preTime_eval (d n inputLength : Nat) :
    (preTime d n).eval inputLength = preBudget d n inputLength inputLength := by
  simp only [preTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, vertexTime_eval, preBudget]

noncomputable def time (d n pushBound tapeCount : Nat) : Polynomial Nat :=
  preTime d n +
    (Polynomial.C 2 *
        (Polynomial.X + Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X) +
      Polynomial.C 6 + Polynomial.C tapeCount *
        (Polynomial.X + preTime d n * Polynomial.C pushBound + Polynomial.X +
          Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X + Polynomial.C 3))

@[simp] theorem time_eval (d n pushBound tapeCount inputLength : Nat) :
    (time d n pushBound tapeCount).eval inputLength =
      totalBudget d n pushBound tapeCount inputLength inputLength := by
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, preTime_eval, totalBudget, finishBudget]

theorem totalBudget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    totalBudget d n pushBound tapeCount vertices inputLength ≤
      (time d n pushBound tapeCount).eval inputLength := by
  rw [time_eval]
  exact totalBudget_mono_vertices d n pushBound tapeCount inputLength hvertices

theorem setup_loop_finish_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    ((3 * vertices + 5) +
        (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)) +
      (2 * (vertices + (2 * d ^ (n + 1)) * vertices) + 6 +
        tapeCount * (inputLength +
          ((3 * vertices + 5) +
            (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)) * pushBound +
          vertices + (2 * d ^ (n + 1)) * vertices + 3)) ≤
      (time d n pushBound tapeCount).eval inputLength := by
  simpa only [totalBudget, preBudget, finishBudget, PoweringTableLayout.blockSize] using
    totalBudget_le_time d n pushBound tapeCount vertices inputLength hvertices

theorem execution_budget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) {preSteps finishSteps : Nat}
    (hpre : preSteps ≤ preBudget d n vertices inputLength)
    (hfinish : finishSteps ≤ finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)) :
    preSteps + finishSteps ≤ (time d n pushBound tapeCount).eval inputLength := by
  calc
    preSteps + finishSteps ≤ totalBudget d n pushBound tapeCount vertices inputLength := by
      unfold totalBudget
      exact Nat.add_le_add hpre hfinish
    _ ≤ (time d n pushBound tapeCount).eval inputLength :=
      totalBudget_le_time d n pushBound tapeCount vertices inputLength hvertices

theorem graph_totalBudget_le_time {vertices d : Nat} (graph : PortTables.Table vertices d)
    (n pushBound tapeCount : Nat) :
    totalBudget d n pushBound tapeCount vertices (PortTables.tableBits graph).length ≤
      (time d n pushBound tapeCount).eval (PortTables.tableBits graph).length :=
  totalBudget_le_time d n pushBound tapeCount vertices (PortTables.tableBits graph).length
    (PortTables.vertices_le_tableBits_length graph)

end DFVSGames.Foundations.Complexity.PoweringPolynomialBudget
end

section

namespace DFVSGames.Foundations.PCP.PortTables

variable {n d : Nat}

def HasPortTails (rows : GraphTables.Rows n (n * d)) : Prop :=
  ∀ i : Fin (n * d), rows[i].tail = ((rowIndex n d).symm i).1

instance (rows : GraphTables.Rows n (n * d)) : Decidable (HasPortTails rows) := by
  unfold HasPortTails
  infer_instance

@[simp] theorem flatRows_hasPortTails (table : Table n d) : HasPortTails (flatRows table) := by
  intro i
  simp [flatRows]

def ofRows (rows : GraphTables.Rows n (n * d)) (valid : GraphTables.Valid rows) : Table n d where
  reverseIndex := Vector.ofFn (fun i => rows[i].reverseIndex)
  relations := Vector.ofFn (fun i => rows[i].relation)
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact valid.1 i
  transpose := by
    intro i a b
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    exact valid.2 i a b

private theorem table_ext_inline_PortTableEncoding {table table' : Table n d}
    (hr : table.reverseIndex = table'.reverseIndex)
    (hp : table.relations = table'.relations) : table = table' := by
  cases table
  cases table'
  cases hr
  cases hp
  rfl

@[simp] theorem ofRows_flatRows (table : Table n d) :
    ofRows (flatRows table) (flatRows_valid table) = table := by
  apply table_ext_inline_PortTableEncoding
  · apply Vector.ext
    intro i hi
    simp [ofRows, flatRows]
  · apply Vector.ext
    intro i hi
    simp [ofRows, flatRows]

def extractInput (ports : Nat) : GraphTables.Table → Option (Input ports)
  | ⟨vertices, darts, rows, valid⟩ =>
      if count_ok : darts = vertices * ports then
        let rows' : GraphTables.Rows vertices (vertices * ports) := count_ok ▸ rows
        let valid' : GraphTables.Valid rows' := by
          cases count_ok
          exact valid
        if HasPortTails rows' then
          some ⟨vertices, ofRows rows' valid'⟩
        else none
      else none

@[simp] theorem extractInput_graphTable (table : Table n d) :
    extractInput d (graphTable table) = some (⟨n, table⟩ : Input d) := by
  simp [extractInput, graphTable]

def decodeInputBits (ports : Nat) (bits : List Bool) : Option (Input ports) :=
  GraphTables.decodeTableBits bits >>= extractInput ports

@[simp] theorem decodeInputBits_inputBits {ports : Nat} (input : Input ports) :
    decodeInputBits ports (inputBits input) = some input := by
  rcases input with ⟨vertices, table⟩
  simp [decodeInputBits, inputBits, tableBits]

def encoding (ports : Nat) : Computability.Encoding (Input ports) Bool where
  encode := inputBits
  decode := decodeInputBits ports
  decode_encode := decodeInputBits_inputBits

theorem inputBits_injective (ports : Nat) : Function.Injective (@inputBits ports) :=
  (encoding ports).encode_injective

end DFVSGames.Foundations.PCP.PortTables
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

def beforeFinish (graph : PortTables.Table vertices d) (n : Nat) : Tape n → List Bool :=
  PoweringMachineOuterLoop.finalTapes graph n (placement n) (outputTape n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)

def finishConfiguration (graph : PortTables.Table vertices d) (n : Nat) : (machine d n).Cfg :=
  ⟨some (finishEntry d n), PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
    beforeFinish graph n⟩

def beforeFinishBudget (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  (3 * vertices + 5) + (vertices *
    (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)

theorem beforeFinish_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (placement n) (beforeFinish graph n) :=
  PoweringMachineOuterLoop.finalTapes_ready graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _)
    (outputTape n) (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)

theorem beforeFinish_output (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (outputTape n) =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_output graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n),
    PoweringMachineOuterLoop.prefixRows_all, PoweringInitializeFrame.prepared_output,
    List.append_nil]

theorem beforeFinish_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerVertices n) = encodeWord vertices := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerVertices n) (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .vertices (by decide)))]
  exact PoweringInitializeFrame.prepared_vertices graph n

theorem beforeFinish_darts (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerDarts n) (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .darts (by decide)))]
  exact PoweringInitializeFrame.prepared_darts graph n

theorem serialized_eq (graph : PortTables.Table vertices d) (n : Nat) :
    encodeWords [vertices, PoweringTableLayout.blockSize d n * vertices] ++
      beforeFinish graph n (outputTape n) = PoweringTables.outputBits graph n := by
  rw [beforeFinish_output, PoweringTableLayout.outputBits_vertexRows]
  congr 2
  rw [PoweringTableLayout.dartCount_eq_vertex_blocks, Nat.mul_comm]

def beforeFinishExecution (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (machine d n).step
      (initList (machine d n) (PortTables.tableBits graph))
      (some (finishConfiguration graph n)) (beforeFinishBudget graph n) := by
  have initialRun := PoweringInitializeFrame.initializeInTime graph n
  have loop := PoweringMachineOuterLoop.loopInTime graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    (guardLabel d n) (bridgeLabel d n) (finishEntry d n) (vertexLabels d n)
    (program d n) (atGuard d n) (atBridge d n) (atVertex d n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)
  rw [PoweringInitializeFrame.prepared_counter] at loop
  simpa only [beforeFinishBudget, Nat.add_comm] using
    (StateTransition.EvalsToInTime.trans (machine d n).step
    (3 * vertices + 5)
    (vertices * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)
    (initList (machine d n) (PortTables.tableBits graph))
    (PoweringInitializeFrame.preparedCfg graph n) (some (finishConfiguration graph n))
    initialRun loop)

def finishSteps (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  PoweringMachineFinish.steps (enumeration n) (outputTape n) (beforeFinish graph n)
    vertices (PoweringTableLayout.blockSize d n * vertices)

def finishExecution (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (machine d n).step (finishConfiguration graph n)
      (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
      (finishSteps graph n) := by
  have run := PoweringMachineFinish.traceAt (enumeration n)
    (headerVertices n) (headerDarts n) (outputTape n)
    (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
    (PoweringGlobalConfiguration.headerVertices_ne_scratch n)
    (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (PoweringGlobalConfiguration.headerDarts_ne_scratch n)
    (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ _)
    (finishLabels d n) (program d n) (atFinish d n)
    (beforeFinish graph n) vertices (PoweringTableLayout.blockSize d n * vertices) [] []
    (by simpa only [List.append_nil] using beforeFinish_vertices graph n)
    (by simpa only [List.append_nil] using beforeFinish_darts graph n)
    (beforeFinish_ready graph n).scratch
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)).1 none
  rw [serialized_eq] at run
  refine { steps := finishSteps graph n, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
  change (advance (TM2.step (program d n)))^[finishSteps graph n]
    (some (finishConfiguration graph n)) = _
  rw [PoweringGlobalConfiguration.haltList_eq]
  simp only [PoweringMasterState.clean, PoweringMasterState.withBuffer] at run
  exact run

def execution (graph : PortTables.Table vertices d) (n : Nat) :
    TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
      (some (PoweringTables.outputBits graph n))
      (beforeFinishBudget graph n + finishSteps graph n) := by
  have run := StateTransition.EvalsToInTime.trans (machine d n).step
    (beforeFinishBudget graph n) (finishSteps graph n)
    (initList (machine d n) (PortTables.tableBits graph))
    (finishConfiguration graph n)
    (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
    (beforeFinishExecution graph n) (finishExecution graph n)
  rw [Nat.add_comm (finishSteps graph n) (beforeFinishBudget graph n)] at run
  exact run

theorem finishSteps_le (graph : PortTables.Table vertices d) (n : Nat) :
    finishSteps graph n ≤
      2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
      PoweringRuntimeBudget.tapeCount n *
        ((PortTables.tableBits graph).length + beforeFinishBudget graph n *
          Runtime.programPushBound (machine d n) + vertices +
          PoweringTableLayout.blockSize d n * vertices + 3) :=
  PoweringRuntimeBudget.finish_steps_le_of_execution d n (PortTables.tableBits graph)
    (finishConfiguration graph n) (beforeFinishBudget graph n) vertices
    (PoweringTableLayout.blockSize d n * vertices) (beforeFinishExecution graph n)

theorem execution_budget_le (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinishBudget graph n + finishSteps graph n ≤
      (PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
        (PoweringRuntimeBudget.tapeCount n)).eval (PortTables.tableBits graph).length := by
  exact PoweringPolynomialBudget.execution_budget_le_time d n
    (Runtime.programPushBound (machine d n)) (PoweringRuntimeBudget.tapeCount n)
    vertices (PortTables.tableBits graph).length (PortTables.vertices_le_tableBits_length graph)
    (Nat.le_refl _) (finishSteps_le graph n)

noncomputable def computableInPolyTime (d n : Nat) :
    TM2ComputableInPolyTime (@PortTables.inputBits d) GenericGraphTables.tableBits
      (PoweringTables.transform d n) where
  tm := machine d n
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
    (PoweringRuntimeBudget.tapeCount n)
  outputsFun input := by
    rcases input with ⟨vertices, graph⟩
    have run := execution graph n
    let bounded : TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
        (some (PoweringTables.outputBits graph n))
        ((PoweringPolynomialBudget.time d n (Runtime.programPushBound (machine d n))
          (PoweringRuntimeBudget.tapeCount n)).eval (PortTables.tableBits graph).length) :=
      ⟨run.toEvalsTo, run.steps_le_m.trans (execution_budget_le graph n)⟩
    change TM2OutputsInTime (machine d n) ((PortTables.tableBits graph).map id)
      (some ((PoweringTables.outputBits graph n).map id)) _
    dsimp only [machine]
    simp only [List.map_id]
    exact bounded

theorem computableInPolyTime_finite_alphabet (d n : Nat) :
    ∀ k, Finite ((computableInPolyTime d n).tm.Γ k) := by
  intro k
  change Finite Bool
  infer_instance

end DFVSGames.Foundations.Complexity.PoweringMachineRuntime
end

section

namespace DFVSGames.Foundations.PCP.RoundComputation

open Turing
open DFVSGames.Foundations.Complexity

abbrev PreprocessingCertificate (H : RoundTables.BaseTable) :=
  TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (PreprocessingTables.output H)

abbrev PoweringCertificate :=
  TM2ComputableInPolyTime
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (GenericGraphTables.tableBits (q := RoundTables.alphabet))
    (PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter)

theorem powered_eq_transform (H : RoundTables.BaseTable) (table : GraphTables.Table) :
    RoundTables.powered H table =
      PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter
        (PreprocessingTables.output H table) := rfl

noncomputable def poweredPolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (GenericGraphTables.tableBits (q := RoundTables.alphabet))
      (RoundTables.powered H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits _
    (fun table => PoweringTables.transform PreprocessingTables.degree
      RoundTables.walkParameter (PreprocessingTables.output H table))
  exact MachineSequential.composeBits preprocessing powering

noncomputable def tablePolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (fun table => AlphabetTable.Table.build (RoundTables.powered H table))
  exact MachineSequential.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)

theorem powered_finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (poweredPolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits preprocessing powering hpreprocessing hpowering

theorem finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)
    (powered_finiteAlphabet H preprocessing powering hpreprocessing hpowering)
    (AlphabetTable.Runtime.finiteAlphabet RoundTables.alphabet)

noncomputable def tablePolynomialTime (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) :=
  tablePolynomialTimeOfCertificates H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter)

theorem tablePolynomialTime_finite_alphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTime H preprocessing).tm :=
  finiteAlphabet H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter) hpreprocessing
    (PoweringMachineRuntime.computableInPolyTime_finite_alphabet
      PreprocessingTables.degree RoundTables.walkParameter)

end DFVSGames.Foundations.PCP.RoundComputation
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
