import OAI.Computability.UniqueGames.Machines.PoweringInitializeFrame
import OAI.Computability.UniqueGames.Machines.PoweringMachineOuterLoopLemmas
import OAI.Computability.UniqueGames.Machines.PoweringMachineVertex
import OAI.Computability.UniqueGames.Machines.Runtime
import OAI.Computability.UniqueGames.PCP.PortTableEncoding

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringPolynomialBudget

open PCP

/-- Initial setup, the actual vertex loop, and the bridge to cleanup. -/
def preBudget (d n vertices inputLength : Nat) : Nat :=
  (3 * vertices + 5) +
    (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)

/-- Cleanup after a preceding run bounded by `prior`, with fixed stack count
and fixed maximum number of pushes per machine transition. -/
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

/-- The exact affine polynomial of one concrete row body. -/
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

/-- The actual fixed number of row commands multiplies the row polynomial. -/
noncomputable def vertexTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringTableLayout.blockSize d n) * rowTime d n

@[simp] theorem vertexTime_eval (d n inputLength : Nat) :
    (vertexTime d n).eval inputLength = PoweringMachineVertex.budget d n inputLength := by
  simp only [vertexTime, Polynomial.eval_mul, Polynomial.eval_C, rowTime_eval,
    PoweringMachineVertex.budget]

/-- Replace the vertex count by the input length in the actual setup/loop bound. -/
noncomputable def preTime (d n : Nat) : Polynomial Nat :=
  (Polynomial.C 3 * Polynomial.X + Polynomial.C 5) +
    (Polynomial.X * (vertexTime d n + Polynomial.C 2) + Polynomial.C 1)

@[simp] theorem preTime_eval (d n inputLength : Nat) :
    (preTime d n).eval inputLength = preBudget d n inputLength inputLength := by
  simp only [preTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, vertexTime_eval, preBudget]

/-- The explicit final polynomial. All coefficients depend only on the fixed
degree/radius and the chosen finite machine's push bound and tape count. -/
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

/-- The actual vertex count may be strictly smaller than the input length. -/
theorem totalBudget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    totalBudget d n pushBound tapeCount vertices inputLength ≤
      (time d n pushBound tapeCount).eval inputLength := by
  rw [time_eval]
  exact totalBudget_mono_vertices d n pushBound tapeCount inputLength hvertices

/-- Direct arithmetic interface for the global setup/loop and cleanup bounds. -/
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

/-- Numerical bounds on two actual phases can use the same fixed polynomial. -/
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

/-- Typed graph input supplies the required vertex-count bound itself. -/
theorem graph_totalBudget_le_time {vertices d : Nat} (graph : PortTables.Table vertices d)
    (n pushBound tapeCount : Nat) :
    totalBudget d n pushBound tapeCount vertices (PortTables.tableBits graph).length ≤
      (time d n pushBound tapeCount).eval (PortTables.tableBits graph).length :=
  totalBudget_le_time d n pushBound tapeCount vertices (PortTables.tableBits graph).length
    (PortTables.vertices_le_tableBits_length graph)

end UniqueGamesTheorem.Foundations.Complexity.PoweringPolynomialBudget

/-!
# Finishing cost from the actual preceding machine execution

Every stack can grow by at most the fixed program's push bound in one
transition. Consequently an actual bounded execution from the standard input
configuration supplies the uniform stack bound needed by the finishing phase.
The bound below uses the same global machine for that preceding execution; no
separate tape-size hypothesis or numerical simulation is substituted for it.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

open Turing

/-- Uniform stack growth along an actual execution, from any initial configuration. -/
theorem stackLength_le_of_execution (tm : FinTM2) (start finish : tm.Cfg)
    (initialBound priorBudget : Nat)
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (prior : StateTransition.EvalsToInTime tm.step start (some finish) priorBudget)
    (k : tm.K) :
    (finish.stk k).length ≤ initialBound + priorBudget * Runtime.programPushBound tm := by
  have grown := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) prior
  exact grown.trans (Nat.add_le_add_right (initial k) _)

/-- Standard input initialization bounds every initial stack by the input length. -/
theorem stackLength_le_from_input (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (finish : tm.Cfg) (priorBudget : Nat)
    (prior : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some finish) priorBudget) (k : tm.K) :
    (finish.stk k).length ≤ input.length + priorBudget * Runtime.programPushBound tm :=
  stackLength_le_of_execution tm (initList tm input) finish input.length priorBudget
    (Runtime.initialStackLength tm input) prior k

/-- Cleanup's concrete tape count is the size of the global tape enumeration. -/
abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

/-- The actual global prefix execution supplies every finishing stack bound.
The physical header premises are used by `PoweringMachineFinish.traceAt`; this
arithmetic consequence of that prefix is valid for any two proposed header values. -/
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

/-- Total transitions of the actual prefix plus the exact finishing cost. -/
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

end UniqueGamesTheorem.Foundations.Complexity.PoweringRuntimeBudget

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

/-- The actual work tapes after all vertex blocks, before final headers. -/
def beforeFinish (graph : PortTables.Table vertices d) (n : Nat) : Tape n → List Bool :=
  PoweringMachineOuterLoop.finalTapes graph n (placement n) (outputTape n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)

def finishConfiguration (graph : PortTables.Table vertices d) (n : Nat) : (machine d n).Cfg :=
  ⟨some (finishEntry d n), PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
    beforeFinish graph n⟩

/-- Initialization and the actual outer loop's proved budgets. -/
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

/-- The serialized result is exactly the actual powering table, including its
header and every relation bit, in the existing output codec. -/
theorem serialized_eq (graph : PortTables.Table vertices d) (n : Nat) :
    encodeWords [vertices, PoweringTableLayout.blockSize d n * vertices] ++
      beforeFinish graph n (outputTape n) = PoweringTables.outputBits graph n := by
  rw [beforeFinish_output, PoweringTableLayout.outputBits_vertexRows]
  congr 2
  rw [PoweringTableLayout.dartCount_eq_vertex_blocks, Nat.mul_comm]

/-- Actual execution from the literal single-input configuration through every
vertex. No graph-dependent instruction or supplied body-execution premise. -/
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

/-- The actual final-copy/cleanup cost on the tapes obtained from the loop. -/
def finishSteps (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  PoweringMachineFinish.steps (enumeration n) (outputTape n) (beforeFinish graph n)
    vertices (PoweringTableLayout.blockSize d n * vertices)

/-- The terminal configuration has precisely the actual output stream and no
remaining work tapes. -/
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
  simpa only [finishConfiguration, finishEntry, finishSteps, PoweringMasterState.clean,
    PoweringMasterState.withBuffer] using! run

/-- Whole-machine execution on the concrete input and output encodings. -/
def execution (graph : PortTables.Table vertices d) (n : Nat) :
    TM2OutputsInTime (machine d n) (PortTables.tableBits graph)
      (some (PoweringTables.outputBits graph n))
      (beforeFinishBudget graph n + finishSteps graph n) := by
  simpa only [TM2OutputsInTime, Option.map_some, Nat.add_comm] using!
    (StateTransition.EvalsToInTime.trans (machine d n).step
    (beforeFinishBudget graph n) (finishSteps graph n)
    (initList (machine d n) (PortTables.tableBits graph))
    (finishConfiguration graph n)
    (some (haltList (machine d n) (PoweringTables.outputBits graph n)))
    (beforeFinishExecution graph n) (finishExecution graph n))

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

/-- A genuine polynomial-time certificate for the actual finite powering
constructor, with the existing concrete codecs on both sides. -/
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
    have input_eq :
        @List.map ((machine d n).Γ (machine d n).k₀)
          ((machine d n).Γ (machine d n).k₀) id (PortTables.tableBits graph) =
          PortTables.tableBits graph := List.map_id _
    have output_eq :
        @List.map ((machine d n).Γ (machine d n).k₁)
          ((machine d n).Γ (machine d n).k₁) id (PoweringTables.outputBits graph n) =
          PoweringTables.outputBits graph n := List.map_id _
    simpa only [input_eq, output_eq, PortTables.inputBits] using bounded

/-- Every work tape, as well as the input/output tapes, has a finite alphabet. -/
theorem computableInPolyTime_finite_alphabet (d n : Nat) :
    ∀ k, Finite ((computableInPolyTime d n).tm.Γ k) := by
  intro k
  change Finite Bool
  infer_instance

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRuntime

end OAI
