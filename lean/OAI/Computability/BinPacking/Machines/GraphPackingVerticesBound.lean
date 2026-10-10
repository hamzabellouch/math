import OAI.Computability.BinPacking.Machines.GraphPackingPreparationFinish

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingVertices

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

def startInputs (x : GraphReductionInput) : Variable → Nat :=
  Function.update
    (Function.update
      (Function.update (GraphPackingPreparation.preparedInputs fixed K x) .labelPower 3)
      .edgePower 1)
    .repetitionOne 0

def startBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  GraphPackingPreparation.baseTapes fixed K x
    (BinaryEncoding.natBits (GraphPackingPreparation.binBound fixed K x)).reverse

def startValues (x : GraphReductionInput) : Register fixed K → Nat :=
  PackingMachineLayout.values (Numerator fixed) denominator (startInputs fixed K x)
    (GraphPackingPreparation.preparedOther fixed K x)

def startTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingCountedProgram.counterTapes (.inr .vertexCounter)
    (PackingMachineLayout.tapes (Numerator fixed) denominator (startBase fixed K x)
      (startInputs fixed K x) (GraphPackingPreparation.preparedOther fixed K x)) x.graph.n

private theorem update_width {α : Type} [DecidableEq α]
    (input : α → Nat) (location : α) (value bound : Nat)
    (hi : ∀ a, (input a).size ≤ bound) (hv : value.size ≤ bound) :
    ∀ a, (Function.update input location value a).size ≤ bound := by
  intro a
  by_cases ha : a = location
  · subst a
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne ha] using hi a

theorem startInputs_width (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (GraphPackingPreparation.preparedInputs fixed K x a).size ≤ width) :
    ∀ a, (startInputs fixed K x a).size ≤ width + 2 := by
  have initial : ∀ a,
      (GraphPackingPreparation.preparedInputs fixed K x a).size ≤ width + 2 := by
    intro a
    exact (hi a).trans (by omega)
  have threeSize : (3 : Nat).size = 2 := by decide
  have oneSize : (1 : Nat).size = 1 := by decide
  have zeroSize : (0 : Nat).size = 0 := by decide
  have first := update_width (GraphPackingPreparation.preparedInputs fixed K x)
    .labelPower 3 (width + 2) initial (by omega)
  have second := update_width (α := Variable) _ .edgePower 1 (width + 2) first (by omega)
  exact update_width (α := Variable) _ .repetitionOne 0 (width + 2) second (by omega)

@[simp] theorem startValues_count_n (x : GraphReductionInput) :
    startValues fixed K x (countRegister fixed K (.input .n)) = x.graph.n := rfl

@[simp] theorem startValues_counter (x : GraphReductionInput) :
    startValues fixed K x (work fixed K .counter) = 0 := rfl

@[simp] theorem startValues_one (x : GraphReductionInput) :
    startValues fixed K x (work fixed K .one) = 0 := rfl

@[simp] theorem startValues_temporary (x : GraphReductionInput) :
    startValues fixed K x (work fixed K .temporary) = 0 := rfl

@[simp] theorem startBase_vertexCounter (x : GraphReductionInput) :
    startBase fixed K x (.inr .vertexCounter) = [] := rfl

def setupPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.setItem fixed K .labelPower 3,
    GraphPackingProgram.setItem fixed K .edgePower 1,
    GraphPackingProgram.setItem fixed K .repetitionOne 0,
    GraphPackingProgram.tally fixed K (.input .n) .vertexCounter]

def setupBound (x : GraphReductionInput) (width : Nat) : Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 3).eval (width + 2) +
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1).eval (width + 2) +
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0).eval (width + 2) +
    BinaryToTallyMachine.runtimeBound x.graph.n + 1

private theorem tally_frame (x : GraphReductionInput) :
    registerTapes (slots fixed K)
      (Function.update (startBase fixed K x) (.inr .vertexCounter)
        (List.replicate x.graph.n true ++ startBase fixed K x (.inr .vertexCounter)))
      (startValues fixed K x) = startTapes fixed K x := by
  rw [startBase_vertexCounter, List.append_nil]
  change registerTapes (slots fixed K)
      (Function.update (startBase fixed K x) (.inr .vertexCounter)
        (List.replicate x.graph.n true)) (startValues fixed K x) =
    Function.update (registerTapes (slots fixed K) (startBase fixed K x)
      (startValues fixed K x)) (.inr .vertexCounter) (List.replicate x.graph.n true)
  exact RegisterFrameEmission.external_update (slots fixed K) (startBase fixed K x)
    (startValues fixed K x) (.inr .vertexCounter)
    (GraphPackingTapeBlocks.slots_outside fixed K .vertexCounter)
    (List.replicate x.graph.n true)

theorem setup_exec (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (GraphPackingPreparation.preparedInputs fixed K x a).size ≤ width)
    (ho : ∀ a, (GraphPackingPreparation.preparedOther fixed K x a).size ≤ width)
    (state : State) :
    ∃ steps ≤ setupBound fixed K x width,
      PhaseRuns (setupPhases fixed K)
        ⟨state, GraphPackingPreparation.preparedTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), startTapes fixed K x⟩ := by
  let initial := GraphPackingPreparation.preparedInputs fixed K x
  let firstInput := Function.update initial .labelPower 3
  let secondInput := Function.update firstInput .edgePower 1
  have initialWidth : ∀ a, (initial a).size ≤ width + 2 := by
    intro a
    exact (hi a).trans (by omega)
  have otherWidth : ∀ a,
      (GraphPackingPreparation.preparedOther fixed K x a).size ≤ width + 2 := by
    intro a
    exact (ho a).trans (by omega)
  have threeSize : (3 : Nat).size = 2 := by decide
  have oneSize : (1 : Nat).size = 1 := by decide
  have firstWidth : ∀ a, (firstInput a).size ≤ width + 2 :=
    update_width initial .labelPower 3 (width + 2) initialWidth (by omega)
  have secondWidth : ∀ a, (secondInput a).size ≤ width + 2 :=
    update_width firstInput .edgePower 1 (width + 2) firstWidth (by omega)
  obtain ⟨firstSteps, firstBound, firstRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 3 (startBase fixed K x) initial
    (GraphPackingPreparation.preparedOther fixed K x) state (width + 2)
    initialWidth otherWidth
  obtain ⟨secondSteps, secondBound, secondRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 (startBase fixed K x) firstInput
    (GraphPackingPreparation.preparedOther fixed K x)
    (.arithmetic (BinaryAddMachine.clean ())) (width + 2) firstWidth otherWidth
  obtain ⟨thirdSteps, thirdBound, thirdRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0 (startBase fixed K x) secondInput
    (GraphPackingPreparation.preparedOther fixed K x)
    (.arithmetic (BinaryAddMachine.clean ())) (width + 2) secondWidth otherWidth
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec
    fixed K (.input .n) .vertexCounter (startBase fixed K x) (startValues fixed K x)
    (.arithmetic (BinaryAddMachine.clean ()))
    (startValues_counter fixed K x) (startValues_one fixed K x)
    (startValues_temporary fixed K x)
  rw [startValues_count_n] at tallyBound tallyRun
  rw [tally_frame] at tallyRun
  have phases : PhaseRuns (setupPhases fixed K)
      ⟨state, GraphPackingPreparation.preparedTapes fixed K x⟩
      (firstSteps + (secondSteps + (thirdSteps + tallySteps)))
      ⟨.arithmetic (BinaryAddMachine.clean ()), startTapes fixed K x⟩ :=
    .cons firstRun (.cons secondRun (.cons thirdRun (PhaseRuns.single tallyRun)))
  refine ⟨firstSteps + (secondSteps + (thirdSteps + tallySteps)), ?_, phases⟩
  unfold setupBound
  omega

end

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open FiniteTapeProgram PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

def data (x : GraphReductionInput) : InventoryData :=
  PackingDescriptorExpression.instantiate fixed x.graph
    (GraphPackingPreparation.repetitions fixed K x) x.k

def inputValues (x : GraphReductionInput) : Variable → Nat :=
  PackingDescriptorExpression.values (data fixed K x) none 0 0

theorem startInputs_eq (x : GraphReductionInput) :
    startInputs fixed K x =
      PackingVertexLoop.vertexInput (inputValues fixed K x) .labelPower 0 := by
  funext a
  cases a <;>
    simp [startInputs, preparedInputs, inputValues, data,
      PackingDescriptorExpression.instantiate, PackingDescriptorExpression.values,
      PackingVertexLoop.vertexInput,
      InventoryData.coordinateDenominator, InventoryData.geometryBound,
      IntegerPackingArithmetic.geomDenominator,
      geometryFactor, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem inputValues_width (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (preparedInputs fixed K x a).size ≤ width) :
    ∀ a, (inputValues fixed K x a).size ≤ width + 2 := by
  intro a
  by_cases h : a = Variable.labelPower
  · subst a
    simp [inputValues, PackingDescriptorExpression.values, NaturalPackingNumerator.labelPower]
  · have bound := startInputs_width fixed K x width hi a
    rw [startInputs_eq, PackingVertexLoop.vertexInput_other _ _ _ _ h] at bound
    exact bound

def emitted (x : GraphReductionInput) : List Bool :=
  PackingDescriptorExpression.rawRecords (PackingInventoryDescriptors.vertexStream (data fixed K x))

theorem stream_eq_emitted (x : GraphReductionInput) :
    PackingVertexLoop.stream (Numerator fixed) denominator
      (PackingInventoryDescriptors.vertexDescriptors fixed)
      (inputValues fixed K x) .labelPower 0 x.graph.n = emitted fixed K x := by
  have numerator_eq : PackingDescriptorExpression.numerator (data fixed K x) = Numerator fixed := by
    funext descriptor
    exact PackingDescriptorExpression.numerator_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k descriptor
  have descriptors_eq : PackingInventoryDescriptors.vertexDescriptors (data fixed K x) =
      PackingInventoryDescriptors.vertexDescriptors fixed :=
    PackingDescriptorExpression.vertexDescriptors_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k
  have count_eq : (data fixed K x).graph.n = x.graph.n := rfl
  have stream := PackingVertexRecords.stream_eq_vertexStream (data fixed K x)
  rw [numerator_eq, descriptors_eq, count_eq] at stream
  simpa only [inputValues, emitted, data, PackingDescriptorExpression.instantiate] using stream

def finalInputs (x : GraphReductionInput) : Variable → Nat :=
  PackingVertexLoop.vertexInput (inputValues fixed K x) .labelPower x.graph.n

def finalBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (startBase fixed K x) (emitted fixed K x)

def finalTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingCountedProgram.counterTapes (.inr .vertexCounter)
    (PackingMachineLayout.tapes (Numerator fixed) denominator (finalBase fixed K x)
      (finalInputs fixed K x) (preparedOther fixed K x)) 0

@[simp] theorem final_labelPower (x : GraphReductionInput) :
    finalInputs fixed K x .labelPower = 3 ^ (x.graph.n + 1) := by
  exact PackingVertexLoop.vertexInput_power _ _ _

@[simp] theorem final_edgePower (x : GraphReductionInput) :
    finalInputs fixed K x .edgePower = 1 := by
  simp [finalInputs, PackingVertexLoop.vertexInput, inputValues, PackingDescriptorExpression.values]

@[simp] theorem final_repetition (x : GraphReductionInput) :
    finalInputs fixed K x .repetitionOne = 0 := by
  simp [finalInputs, PackingVertexLoop.vertexInput, inputValues, PackingDescriptorExpression.values]

@[simp] theorem final_counter_empty (x : GraphReductionInput) :
    finalTapes fixed K x (.inr .vertexCounter) = [] := by
  simp [finalTapes, PackingCountedProgram.counterTapes]

@[simp] theorem final_output (x : GraphReductionInput) :
    finalTapes fixed K x (.inr .reverseOutput) =
      (emitted fixed K x).reverse ++
        (BinaryEncoding.natBits (binBound fixed K x)).reverse := by
  simp [finalTapes, PackingCountedProgram.counterTapes, finalBase, outputTapes,
    PackingMachineLayout.tapes_extra, startBase, baseTapes]

theorem finalTapes_eq_frame (x : GraphReductionInput) :
    finalTapes fixed K x =
      PackingMachineLayout.tapes (Numerator fixed) denominator (finalBase fixed K x)
        (finalInputs fixed K x) (preparedOther fixed K x) := by
  have empty : PackingMachineLayout.tapes (Numerator fixed) denominator (finalBase fixed K x)
      (finalInputs fixed K x) (preparedOther fixed K x) (.inr .vertexCounter) = [] := by
    simp [PackingMachineLayout.tapes_extra, finalBase, outputTapes, startBase, baseTapes]
  funext tape
  by_cases h : tape = .inr .vertexCounter
  · subst tape
    simp only [final_counter_empty, empty]
  · simp [finalTapes, PackingCountedProgram.counterTapes, h]

def loopBudget (_K : Nat) (x : GraphReductionInput) (width : Nat) : Nat :=
  x.graph.n * ((PackingVertexLoop.bodyTimePolynomial (Numerator fixed) denominator
    (PackingInventoryDescriptors.vertexDescriptors fixed)).eval
      (PackingVertexLoop.aggregateWidth (width + 2) 0 x.graph.n) + 1) + 1

theorem loop_exec (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (preparedInputs fixed K x a).size ≤ width) :
    ∃ steps ≤ loopBudget fixed K x width,
      Exec (PackingVertexLoop.code (Numerator fixed) denominator
        (PackingInventoryDescriptors.vertexDescriptors fixed) .labelPower
        (GraphPackingProgram.otherSetup fixed K .three) (.inr Work.temporary)
        (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .vertexCounter)
        ⟨.arithmetic (BinaryAddMachine.clean ()), startTapes fixed K x⟩ steps
        ⟨PackingCountedProgram.guardState none, finalTapes fixed K x⟩ := by
  have hthree : preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K .three) = 3 := rfl
  have htemp : preparedOther fixed K x (.inr Work.temporary) = 0 := rfl
  have run := PackingVertexLoop.exec (Numerator fixed) denominator
    (PackingInventoryDescriptors.vertexDescriptors fixed) .labelPower
    (GraphPackingProgram.otherSetup fixed K .three) (.inr Work.temporary)
    (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .vertexCounter (by decide)
    (startBase fixed K x) (inputValues fixed K x) (preparedOther fixed K x) hthree htemp
    0 x.graph.n (width + 2) (inputValues_width fixed K x width hi)
    (.arithmetic (BinaryAddMachine.clean ()))
  simpa only [loopBudget, startTapes, startInputs_eq, stream_eq_emitted,
    finalTapes, finalBase, finalInputs, Nat.zero_add] using run

def phaseBudget (x : GraphReductionInput) (width : Nat) : Nat :=
  setupBound fixed K x width + loopBudget fixed K x width + 1

theorem exec (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (preparedInputs fixed K x a).size ≤ width)
    (ho : ∀ a, (preparedOther fixed K x a).size ≤ width) (state : State) :
    ∃ steps ≤ phaseBudget fixed K x width,
      Exec (GraphPackingProgram.vertices fixed K)
        ⟨state, preparedTapes fixed K x⟩ steps
        ⟨PackingCountedProgram.guardState none, finalTapes fixed K x⟩ := by
  obtain ⟨setupSteps, setupBound, setupRun⟩ := setup_exec fixed K x width hi ho state
  obtain ⟨loopSteps, loopBound, loopRun⟩ := loop_exec fixed K x width hi
  have runs := setupRun.append (GraphPackingProgram.PhaseRuns.single loopRun)
  refine ⟨setupSteps + loopSteps + 1, ?_, ?_⟩
  · unfold phaseBudget
    omega
  · simpa only [GraphPackingProgram.vertices, setupPhases, List.cons_append, List.nil_append]
      using runs.toExec

end BinPackingGap.GraphPackingVertices

namespace BinPackingGap.GraphPackingVerticesBound

open FiniteTapeProgram PackingMachineBlocks
open GraphPackingRegisters PackingItemExpression
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def setPolynomial : Polynomial Nat :=
  PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 3 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0

def bodyPolynomial : Polynomial Nat :=
  PackingVertexLoop.bodyTimePolynomial (Numerator fixed) denominator
    (PackingInventoryDescriptors.vertexDescriptors fixed)

def polynomial : Polynomial Nat :=
  (setPolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K + 2) +
    40 * (Polynomial.X + 1) ^ 3 + 1 +
    Polynomial.X *
      ((bodyPolynomial fixed).comp
        (GraphPackingWidths.polynomial fixed K + 2 * Polynomial.X + 5) + 1) + 1 + 1

theorem polynomial_eval (size : Nat) :
    (polynomial fixed K).eval size =
      (setPolynomial fixed K).eval ((GraphPackingWidths.polynomial fixed K).eval size + 2) +
        40 * (size + 1) ^ 3 + 1 +
        size * ((bodyPolynomial fixed).eval
          ((GraphPackingWidths.polynomial fixed K).eval size + 2 * size + 5) + 1) + 1 + 1 := by
  simp [polynomial]

private theorem tallyBound_le (n size : Nat) (hn : n ≤ size) :
    BinaryToTallyMachine.runtimeBound n ≤ 40 * (size + 1) ^ 3 := by
  have hs : n.size ≤ size := (nat_size_le_self n).trans hn
  calc
    BinaryToTallyMachine.runtimeBound n = 40 * (n + 1) * (n.size + 1) ^ 2 := rfl
    _ ≤ 40 * (size + 1) * (size + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hn 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2)
    _ = 40 * (size + 1) ^ 3 := by ring

theorem phaseBudget_le (x : GraphReductionInput) :
    GraphPackingVertices.phaseBudget fixed K x (GraphPackingWidths.width fixed K x) ≤
      (polynomial fixed K).eval (graphBits x).length := by
  let size := (graphBits x).length
  let width := GraphPackingWidths.width fixed K x
  have hn : x.graph.n ≤ size := graph_vertexCount_le_bits x
  have tally := tallyBound_le x.graph.n size hn
  have setup : GraphPackingVertices.setupBound fixed K x width ≤
      (setPolynomial fixed K).eval (width + 2) + 40 * (size + 1) ^ 3 + 1 := by
    simp only [GraphPackingVertices.setupBound, setPolynomial, Polynomial.eval_add]
    omega
  have aggregate : PackingVertexLoop.aggregateWidth (width + 2) 0 x.graph.n ≤
      width + 2 * size + 5 := by
    unfold PackingVertexLoop.aggregateWidth
    omega
  have body := MachineComposition.natPolynomial_eval_mono (bodyPolynomial fixed) aggregate
  have product := Nat.mul_le_mul hn (Nat.add_le_add_right body 1)
  have loop : GraphPackingVertices.loopBudget fixed K x width ≤
      size * ((bodyPolynomial fixed).eval (width + 2 * size + 5) + 1) + 1 := by
    simpa only [GraphPackingVertices.loopBudget, bodyPolynomial] using
      Nat.add_le_add_right product 1
  rw [polynomial_eval]
  change GraphPackingVertices.setupBound fixed K x width +
      GraphPackingVertices.loopBudget fixed K x width + 1 ≤
    (setPolynomial fixed K).eval (width + 2) + 40 * (size + 1) ^ 3 + 1 +
      size * ((bodyPolynomial fixed).eval (width + 2 * size + 5) + 1) + 1 + 1
  omega

theorem exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (polynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.vertices fixed K)
        ⟨state, GraphPackingPreparation.preparedTapes fixed K x⟩ steps
        ⟨PackingCountedProgram.guardState none, GraphPackingVertices.finalTapes fixed K x⟩ := by
  obtain ⟨steps, bound, run⟩ := GraphPackingVertices.exec fixed K x
    (GraphPackingWidths.width fixed K x)
    (GraphPackingWidths.preparedInputs_width fixed K x)
    (GraphPackingWidths.preparedOther_width fixed K x) state
  exact ⟨steps, bound.trans (phaseBudget_le fixed K x), run⟩

end BinPackingGap.GraphPackingVerticesBound

end

end OAI
