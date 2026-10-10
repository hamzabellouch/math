import OAI.Computability.BinPacking.Machines.GraphPackingJobCleanup

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingProgram

open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

def endpointResultValues (right : Bool) (vals : Register fixed K → Nat) (v : Nat) :
    Register fixed K → Nat := by
  classical
  exact Function.update
    (Function.update vals (endpointRegisters fixed K right 0) v)
    (endpointRegisters fixed K right 2) (3 ^ (v + 1))

def endpointResultTapes (right : Bool) (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (v : Nat) (suffix : List Bool) :
    Tape fixed K → List Bool :=
  registerTapes (slots fixed K) (Function.update base (.inr .endpoints) suffix)
    (endpointResultValues fixed K right vals v)

private theorem endpoint_frame_extra (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (e : Extra) :
    registerTapes (slots fixed K) base vals (.inr e) = base (.inr e) := by
  apply registerTapes_other
  rintro ⟨i, hi⟩
  cases hi

private theorem endpoint_extra_outside (e : Extra) (i : Register fixed K ⊕ Fin 6) :
    slots fixed K i ≠ Sum.inr e := by
  simp [slots, PackingMachineLayout.registers]

theorem endpoint_exec (right : Bool) (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (v : Nat) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = BinaryEncoding.natBits v ++ suffix)
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = [])
    (initialRegisters : ∀ i : Fin 7,
      vals (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i)
    (state : State) :
    ∃ steps ≤ 2 * v.size + 4 + PackingEndpointPower.timePolynomial.eval v,
      Exec (endpoint fixed K right)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          endpointResultTapes fixed K right base vals v suffix⟩ := by
  classical
  let start := registerTapes (slots fixed K) base vals
  let afterBase := Function.update base (.inr .endpoints) suffix
  let afterVals := Function.update vals (endpointRegisters fixed K right 0) v
  let decoded := registerTapes (slots fixed K) afterBase afterVals
  have selectedZero : vals (endpointRegisters fixed K right 0) = 0 := by
    simpa [PackingEndpointPower.values] using initialRegisters 0
  have source : start (decoderSlots fixed K right 0) =
      BinaryEncoding.natBits v ++ suffix := by
    change registerTapes (slots fixed K) base vals (.inr .endpoints) = _
    rw [endpoint_frame_extra]
    exact sourceWord
  have scratch : start (decoderSlots fixed K right 1) = [] := by
    change registerTapes (slots fixed K) base vals (.inr .decodeScratch) = []
    rw [endpoint_frame_extra]
    exact decodeScratch
  have destination : start (slots fixed K (.inl (endpointRegisters fixed K right 0))) =
      [] := by
    simp only [start, registerTapes_reg, selectedZero, Nat.zero_bits]
  have decodedFrame :
      PackingFieldDecodeMachine.decodedTapes (decoderSlots fixed K right)
        start v.bits suffix = decoded := by
    change Function.update (Function.update start (.inr .endpoints) suffix)
      (slots fixed K (.inl (endpointRegisters fixed K right 0)))
      (v.bits ++ start (slots fixed K (.inl (endpointRegisters fixed K right 0)))) = _
    rw [destination, List.append_nil]
    change Function.update
      (Function.update (registerTapes (slots fixed K) base vals) (.inr .endpoints) suffix)
      (slots fixed K (.inl (endpointRegisters fixed K right 0))) v.bits = _
    rw [← external_update (slots fixed K) base vals (.inr .endpoints)
      (endpoint_extra_outside fixed K .endpoints) suffix]
    exact registerTapes_update (slots fixed K) afterBase vals
      (endpointRegisters fixed K right 0) v
  have decodedRun := PackingFieldDecodeMachine.decodeNat_exec
    (decoderSlots fixed K right) start () v suffix source scratch
  rw [decodedFrame] at decodedRun
  have first := PackingArithmeticProgram.exec
    (PackingFieldDecodeMachine.code (decoderSlots fixed K right)) start decoded
    (2 * v.size + 2) state decodedRun
  have afterRegisters : ∀ i : Fin 7,
      afterVals (endpointRegisters fixed K right i) = PackingEndpointPower.values v 0 i := by
    intro i
    have hi (a b : Fin 7) : endpointRegisters fixed K right a =
        endpointRegisters fixed K right b ↔ a = b :=
      (endpointRegisters fixed K right).injective.eq_iff
    fin_cases i <;>
      simp [afterVals, hi, initialRegisters, PackingEndpointPower.values]
  have ready : PackingEndpointPower.Ready (endpointSlots fixed K right)
      (.inr .powerCounter) decoded v := by
    constructor
    · intro i
      change registerTapes (slots fixed K) afterBase afterVals
        (slots fixed K (.inl (endpointRegisters fixed K right i))) = _
      rw [registerTapes_reg, afterRegisters]
    · intro j
      change registerTapes (slots fixed K) afterBase afterVals (slots fixed K (.inr j)) = []
      exact registerTapes_scratch (slots fixed K) afterBase afterVals j
    · change registerTapes (slots fixed K) afterBase afterVals (.inr .powerCounter) = []
      rw [endpoint_frame_extra]
      simpa [afterBase] using powerCounter
  obtain ⟨powerSteps, powerBound, second⟩ := PackingEndpointPower.exec
    (endpointSlots fixed K right) (.inr .powerCounter)
    (endpoint_outside fixed K right .powerCounter) decoded v ready
    (.arithmetic (BinaryAddMachine.clean ()))
  have finalFrame : PackingEndpointPower.resultTapes (endpointSlots fixed K right) decoded v =
      endpointResultTapes fixed K right base vals v suffix := by
    change Function.update (registerTapes (slots fixed K) afterBase afterVals)
      (slots fixed K (.inl (endpointRegisters fixed K right 2))) (3 ^ (v + 1)).bits = _
    exact registerTapes_update (slots fixed K) afterBase afterVals
      (endpointRegisters fixed K right 2) (3 ^ (v + 1))
  rw [finalFrame] at second
  have phases := PhaseRuns.cons first (PhaseRuns.single second)
  refine ⟨(1 + (2 * v.size + 2)) + powerSteps + 1, by omega, ?_⟩
  simpa only [endpoint] using phases.toExec

def endpointTimePolynomial : Polynomial Nat :=
  PackingEndpointPower.timePolynomial + Polynomial.X + Polynomial.C 3

theorem endpoint_exec_polynomial (right : Bool) (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (v : Nat) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = BinaryEncoding.natBits v ++ suffix)
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = [])
    (initialRegisters : ∀ i : Fin 7,
      vals (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i)
    (state : State) :
    ∃ steps ≤ endpointTimePolynomial.eval (v + (BinaryEncoding.natBits v).length),
      Exec (endpoint fixed K right)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          endpointResultTapes fixed K right base vals v suffix⟩ := by
  obtain ⟨steps, bound, run⟩ := endpoint_exec fixed K right base vals v suffix
    sourceWord decodeScratch powerCounter initialRegisters state
  refine ⟨steps, bound.trans ?_, run⟩
  have monotone := MachineComposition.natPolynomial_eval_mono
    PackingEndpointPower.timePolynomial
    (Nat.le_add_right v (BinaryEncoding.natBits v).length)
  have fieldLength := BinaryEncoding.natBits_length v
  simp only [endpointTimePolynomial, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  omega

theorem endpoint_layout_exec (right : Bool) (base : Tape fixed K → List Bool)
    (input : PackingItemExpression.Variable → Nat) (other : Other fixed K → Nat)
    (v : Nat) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = BinaryEncoding.natBits v ++ suffix)
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = [])
    (initialRegisters : ∀ i : Fin 7,
      PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input other
        (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i)
    (state : State) :
    ∃ steps ≤ endpointTimePolynomial.eval (v + (BinaryEncoding.natBits v).length),
      Exec (endpoint fixed K right)
        ⟨state, PackingMachineLayout.tapes (Numerator fixed)
          PackingItemExpression.denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          PackingMachineLayout.tapes (Numerator fixed) PackingItemExpression.denominator
            (Function.update base (.inr .endpoints) suffix) input
            (Function.update (Function.update other
              (.inr (if right then Work.rightEndpoint else Work.leftEndpoint)) v)
              (.inr (if right then Work.rightPower else Work.leftPower)) (3 ^ (v + 1)))⟩ := by
  classical
  have updates : endpointResultValues fixed K right
      (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input other) v =
      PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input
        (Function.update (Function.update other
          (.inr (if right then Work.rightEndpoint else Work.leftEndpoint)) v)
          (.inr (if right then Work.rightPower else Work.leftPower)) (3 ^ (v + 1))) := by
    simp only [endpointResultValues, PackingMachineLayout.values_update_other]
    rfl
  obtain ⟨steps, bound, run⟩ := endpoint_exec_polynomial fixed K right base
    (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator input other)
    v suffix sourceWord decodeScratch powerCounter initialRegisters state
  refine ⟨steps, bound, ?_⟩
  unfold endpointResultTapes at run
  rw [updates] at run
  exact run

end BinPackingGap.GraphPackingProgram

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes values)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def repeatPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.setItem fixed K .repetitionOne 1,
    GraphPackingProgram.tally fixed K (.output .repetitions) .repetitionCounter,
    PackingJobLoop.code (Numerator fixed) denominator
      (PackingInventoryDescriptors.jobDescriptors fixed)
      .labelPower .repetitionOne (by decide)
      (.inr Work.leftPower) (.inr Work.rightPower)
      (GraphPackingProgram.otherSetup fixed K .one) (.inr Work.temporary)
      (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .repetitionCounter]

def repeatSetPolynomial : Polynomial Nat :=
  PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .repetitionOne 1

def repeatLoopPolynomial : Polynomial Nat :=
  PackingJobLoop.timePolynomial (Numerator fixed) denominator
    (PackingInventoryDescriptors.jobDescriptors fixed) .labelPower
    (.inr Work.leftPower : Other fixed K) (.inr Work.rightPower)

def repeatWidthPolynomial : Polynomial Nat :=
  repeatSetPolynomial fixed K + 40 * (Polynomial.X + 1) ^ 3 + 1 +
    (repeatLoopPolynomial fixed K).comp (3 * Polynomial.X + 2)

def repeatTimePolynomial : Polynomial Nat :=
  (repeatWidthPolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K)

theorem repeatTimePolynomial_eval (x : GraphReductionInput) :
    (repeatTimePolynomial fixed K).eval (graphBits x).length =
      (repeatSetPolynomial fixed K).eval (GraphPackingWidths.width fixed K x) +
      40 * (GraphPackingWidths.width fixed K x + 1) ^ 3 + 1 +
      (repeatLoopPolynomial fixed K).eval (3 * GraphPackingWidths.width fixed K x + 2) := by
  simp [repeatTimePolynomial, repeatWidthPolynomial, GraphPackingWidths.width]

private theorem repeat_tally_bound (n width : Nat) (hn : n ≤ width) :
    BinaryToTallyMachine.runtimeBound n ≤ 40 * (width + 1) ^ 3 := by
  have hs : n.size ≤ width := (nat_size_le_self n).trans hn
  calc
    BinaryToTallyMachine.runtimeBound n = 40 * (n + 1) * (n.size + 1) ^ 2 := rfl
    _ ≤ 40 * (width + 1) * (width + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hn 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2)
    _ = 40 * (width + 1) ^ 3 := by ring

theorem repeat_exec (x : GraphReductionInput) (edge : x.graph.Edge)
    (base : Tape fixed K → List Bool) (state : State)
    (counterEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ (repeatTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (repeatPhases fixed K)
        ⟨state, tapes (Numerator fixed) denominator base (inputs fixed K x edge.val)
          (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ steps
        ⟨guardState none, tapes (Numerator fixed) denominator
          (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
          (repeatFinalInputs fixed K x edge)
          (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ := by
  let width := GraphPackingWidths.width fixed K x
  let count := GraphPackingPreparation.repetitions fixed K x
  let other := loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val
  let input := repeatInputs fixed K x edge.val
  let vals := values (Numerator fixed) denominator input other
  have inputWidth : ∀ a, (input a).size ≤ width :=
    repeatInputs_width fixed K x edge.val (Nat.le_of_lt edge.isLt)
  have otherWidth : ∀ r, (other r).size ≤ width :=
    loadedOther_width fixed K x _ _ (x.graph.left edge).isLt (x.graph.right edge).isLt
  have initialWidth : ∀ a, (inputs fixed K x edge.val a).size ≤ width :=
    inputs_width fixed K x edge.val (Nat.le_of_lt edge.isLt)
  obtain ⟨setSteps, setBound, setRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 1 base (inputs fixed K x edge.val)
    other state width initialWidth otherWidth
  have sourceValue : vals (countRegister fixed K (.output .repetitions)) = count :=
    loaded_repetitions fixed K x _ _
  have counterZero : vals (work fixed K .counter) = 0 :=
    loaded_helper_zero fixed K x _ _ .counter (Or.inl rfl)
  have oneZero : vals (work fixed K .one) = 0 :=
    loaded_helper_zero fixed K x _ _ .one (Or.inr (Or.inl rfl))
  have temporaryZero : vals (work fixed K .temporary) = 0 :=
    loaded_helper_zero fixed K x _ _ .temporary (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec
    fixed K (.output .repetitions) .repetitionCounter base vals
    (.arithmetic (BinaryAddMachine.clean ())) counterZero oneZero temporaryZero
  rw [sourceValue] at tallyBound
  have tallyFrame : registerTapes (slots fixed K)
      (Function.update base (.inr .repetitionCounter)
        (List.replicate count true ++ base (.inr .repetitionCounter))) vals =
      counterTapes (.inr .repetitionCounter)
        (tapes (Numerator fixed) denominator base input other) count := by
    rw [counterEmpty, List.append_nil]
    exact RegisterFrameEmission.external_update (slots fixed K) base vals
      (.inr .repetitionCounter) (GraphPackingTapeBlocks.slots_outside fixed K .repetitionCounter)
      (List.replicate count true)
  rw [sourceValue, tallyFrame] at tallyRun
  have hone : other (GraphPackingProgram.otherSetup fixed K .one) = 1 :=
    loaded_one fixed K x _ _
  have htemp : other (.inr .temporary) = 0 := temporaryZero
  obtain ⟨loopSteps, loopBound, loopRun⟩ := PackingJobLoop.exec_polynomial
    (Numerator fixed) denominator (PackingInventoryDescriptors.jobDescriptors fixed)
    .labelPower .repetitionOne (by decide)
    (.inr Work.leftPower) (.inr Work.rightPower)
    (GraphPackingProgram.otherSetup fixed K .one) (.inr Work.temporary)
    (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .repetitionCounter (by decide)
    base input other hone htemp count width width inputWidth otherWidth
    (.arithmetic (BinaryAddMachine.clean ()))
  have streamEq := repeatStream_eq fixed K x edge
  have inputEq := repeatIteration_eq fixed K x edge
  change PackingJobLoop.stream (Numerator fixed) denominator
      (PackingInventoryDescriptors.jobDescriptors fixed) input .labelPower .repetitionOne
      (other (.inr Work.leftPower)) (other (.inr Work.rightPower)) count =
    edgeWord fixed K x edge at streamEq
  change PackingJobLoop.iterationInput input .labelPower .repetitionOne
      (other (.inr Work.rightPower)) count = repeatFinalInputs fixed K x edge at inputEq
  rw [streamEq, inputEq] at loopRun
  have finalCounter : (tapes (Numerator fixed) denominator
      (outputTapes (.inr Extra.reverseOutput) base (edgeWord fixed K x edge))
      (repeatFinalInputs fixed K x edge) other) (.inr .repetitionCounter) = [] := by
    simp [outputTapes, counterEmpty]
  have cleared : counterTapes (.inr Extra.repetitionCounter)
      (tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
        (repeatFinalInputs fixed K x edge) other) 0 =
      tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
        (repeatFinalInputs fixed K x edge) other := by
    simp only [counterTapes, List.replicate_zero]
    rw [← finalCounter, Function.update_eq_self]
  rw [cleared] at loopRun
  have phases : PhaseRuns (repeatPhases fixed K)
      ⟨state, tapes (Numerator fixed) denominator base (inputs fixed K x edge.val) other⟩
      (setSteps + (tallySteps + loopSteps))
      ⟨guardState none, tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
        (repeatFinalInputs fixed K x edge) other⟩ :=
    .cons setRun (.cons tallyRun (PhaseRuns.single loopRun))
  refine ⟨setSteps + (tallySteps + loopSteps), ?_, phases⟩
  have hc : count ≤ width := Nat.le_trans (Nat.le_succ count)
    (GraphPackingWidths.repetitions_width fixed K x)
  have tallyUpper := repeat_tally_bound count width hc
  have aggregate : PackingJobLoop.aggregateWidth width width count ≤ 3 * width + 2 := by
    unfold PackingJobLoop.aggregateWidth
    omega
  have loopUpper := MachineComposition.natPolynomial_eval_mono
    (repeatLoopPolynomial fixed K) aggregate
  change loopSteps ≤ (repeatLoopPolynomial fixed K).eval
    (PackingJobLoop.aggregateWidth width width count) at loopBound
  change setSteps ≤ (repeatSetPolynomial fixed K).eval width at setBound
  rw [repeatTimePolynomial_eval]
  change setSteps + (tallySteps + loopSteps) ≤
    (repeatSetPolynomial fixed K).eval width + 40 * (width + 1) ^ 3 + 1 +
      (repeatLoopPolynomial fixed K).eval (3 * width + 2)
  omega

end

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes values)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def prefixPhases : List (GraphPackingProgram.Program fixed K) :=
  [.atom (.pop (.inr .endpoints) (fun state _ => state) .done),
    GraphPackingProgram.endpoint fixed K false,
    GraphPackingProgram.endpoint fixed K true]

def prefixTimePolynomial : Polynomial Nat :=
  1 + 2 * GraphPackingProgram.endpointTimePolynomial.comp (4 * (Polynomial.X + 1))

theorem prefixTimePolynomial_eval (s : Nat) :
    prefixTimePolynomial.eval s =
      1 + 2 * GraphPackingProgram.endpointTimePolynomial.eval (4 * (s + 1)) := by
  simp [prefixTimePolynomial]

private theorem prepared_endpoint_registers (x : GraphReductionInput)
    (input : Variable → Nat) (right : Bool) :
    ∀ i : Fin 7, values (Numerator fixed) denominator input (preparedOther fixed K x)
      (endpointRegisters fixed K right i) = PackingEndpointPower.values 0 0 i := by
  intro i
  cases right <;> fin_cases i <;> rfl

private theorem right_after_left_registers (x : GraphReductionInput)
    (input : Variable → Nat) (left : Nat) :
    ∀ i : Fin 7, values (Numerator fixed) denominator input
      (loadEndpoint fixed K (preparedOther fixed K x) false left)
      (endpointRegisters fixed K true i) = PackingEndpointPower.values 0 0 i := by
  intro i
  fin_cases i <;> rfl

private theorem endpoint_measure_le (x : GraphReductionInput) (v : x.graph.Vertex) :
    v.val + (BinaryEncoding.natBits v.val).length ≤ 4 * ((graphBits x).length + 1) := by
  have hv : v.val ≤ (graphBits x).length :=
    (Nat.le_of_lt v.isLt).trans (graph_vertexCount_le_bits x)
  have hs : v.val.size ≤ v.val := nat_size_le_self v.val
  rw [BinaryEncoding.natBits_length]
  omega

theorem prefix_exec (x : GraphReductionInput) (edge : x.graph.Edge)
    (base : Tape fixed K → List Bool) (input : Variable → Nat)
    (suffix : List Bool) (state : State)
    (sourceWord : base (.inr .endpoints) = true ::
      (BinaryEncoding.natBits (x.graph.left edge).val ++
        (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)))
    (decodeScratch : base (.inr .decodeScratch) = [])
    (powerCounter : base (.inr .powerCounter) = []) :
    ∃ steps ≤ prefixTimePolynomial.eval (graphBits x).length,
      PhaseRuns (prefixPhases fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator (Function.update base (.inr .endpoints) suffix)
            input (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ := by
  let remainder := BinaryEncoding.natBits (x.graph.left edge).val ++
    (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)
  let afterMarker := Function.update base (.inr Extra.endpoints) remainder
  let afterLeft := Function.update base (.inr Extra.endpoints)
    (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)
  let leftOther := loadEndpoint fixed K (preparedOther fixed K x) false (x.graph.left edge).val
  have markerFrame : Function.update
      (tapes (Numerator fixed) denominator base input (preparedOther fixed K x))
      (.inr Extra.endpoints) remainder =
      tapes (Numerator fixed) denominator afterMarker input (preparedOther fixed K x) := by
    exact (RegisterFrameEmission.external_update (slots fixed K) base
      (values (Numerator fixed) denominator input (preparedOther fixed K x))
      (.inr Extra.endpoints)
      (by intro q; simp [slots, PackingMachineLayout.registers]) remainder).symm
  have markerRun : Exec
      (.atom (.pop (.inr Extra.endpoints) (fun state _ => state) .done))
      ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩ 1
      ⟨state, tapes (Numerator fixed) denominator afterMarker input (preparedOther fixed K x)⟩ := by
    have actual := Exec.atom
      (Action.pop (.inr Extra.endpoints) (fun state _ => state) .done)
      ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩
    simp only [Action.eval, PackingMachineLayout.tapes_extra, sourceWord,
      List.tail_cons] at actual
    change Exec _ _ 1 ⟨state, Function.update
      (tapes (Numerator fixed) denominator base input (preparedOther fixed K x))
      (.inr Extra.endpoints) remainder⟩ at actual
    rw [markerFrame] at actual
    exact actual
  have leftSource : afterMarker (.inr .endpoints) =
      BinaryEncoding.natBits (x.graph.left edge).val ++
        (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix) := by simp [afterMarker, remainder]
  have leftScratch : afterMarker (.inr .decodeScratch) = [] := by
    simpa [afterMarker] using decodeScratch
  have leftCounter : afterMarker (.inr .powerCounter) = [] := by
    simpa [afterMarker] using powerCounter
  obtain ⟨leftSteps, leftBound, leftRun⟩ := GraphPackingProgram.endpoint_layout_exec fixed K
    false afterMarker input (preparedOther fixed K x) (x.graph.left edge).val
    (BinaryEncoding.natBits (x.graph.right edge).val ++ suffix)
    leftSource leftScratch leftCounter (prepared_endpoint_registers fixed K x input false) state
  have leftRun' : Exec (GraphPackingProgram.endpoint fixed K false)
      ⟨state, tapes (Numerator fixed) denominator afterMarker input (preparedOther fixed K x)⟩
      leftSteps ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator afterLeft input leftOther⟩ := by
    simpa [afterMarker, afterLeft, leftOther, loadEndpoint, endpointWork, powerWork,
      Function.update_idem] using leftRun
  have rightSource : afterLeft (.inr .endpoints) =
      BinaryEncoding.natBits (x.graph.right edge).val ++ suffix := by simp [afterLeft]
  have rightScratch : afterLeft (.inr .decodeScratch) = [] := by
    simpa [afterLeft] using decodeScratch
  have rightCounter : afterLeft (.inr .powerCounter) = [] := by
    simpa [afterLeft] using powerCounter
  obtain ⟨rightSteps, rightBound, rightRun⟩ := GraphPackingProgram.endpoint_layout_exec fixed K
    true afterLeft input leftOther (x.graph.right edge).val suffix rightSource rightScratch
    rightCounter (right_after_left_registers fixed K x input (x.graph.left edge).val)
    (.arithmetic (BinaryAddMachine.clean ()))
  have rightRun' : Exec (GraphPackingProgram.endpoint fixed K true)
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator afterLeft input leftOther⟩ rightSteps
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator (Function.update base (.inr .endpoints) suffix)
          input (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ := by
    simpa [afterLeft, loadedOther, leftOther, loadEndpoint, endpointWork, powerWork,
      Function.update_idem] using rightRun
  have phases : PhaseRuns (prefixPhases fixed K)
      ⟨state, tapes (Numerator fixed) denominator base input (preparedOther fixed K x)⟩
      (1 + (leftSteps + rightSteps))
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator (Function.update base (.inr .endpoints) suffix)
          input (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ :=
    .cons markerRun (.cons leftRun' (PhaseRuns.single rightRun'))
  refine ⟨1 + (leftSteps + rightSteps), ?_, phases⟩
  have leftUpper := MachineComposition.natPolynomial_eval_mono
    GraphPackingProgram.endpointTimePolynomial (endpoint_measure_le x (x.graph.left edge))
  have rightUpper := MachineComposition.natPolynomial_eval_mono
    GraphPackingProgram.endpointTimePolynomial (endpoint_measure_le x (x.graph.right edge))
  rw [prefixTimePolynomial_eval]
  omega

end

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

def resultBase (base : Tape fixed K → List Bool) (suffix word : List Bool) :
    Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (Function.update base (.inr .endpoints) suffix) word

@[simp] theorem resultBase_endpoints (base : Tape fixed K → List Bool)
    (suffix word : List Bool) : resultBase fixed K base suffix word (.inr .endpoints) = suffix := by
  simp [resultBase, outputTapes]

@[simp] theorem resultBase_other (base : Tape fixed K → List Bool)
    (suffix word : List Bool) (e : Extra) (hne : e ≠ .endpoints) (hno : e ≠ .reverseOutput) :
    resultBase fixed K base suffix word (.inr e) = base (.inr e) := by
  simp [resultBase, outputTapes, hne, hno]

theorem resultBase_append (base : Tape fixed K → List Bool)
    (firstSuffix finalSuffix firstWord secondWord : List Bool) :
    resultBase fixed K (resultBase fixed K base firstSuffix firstWord) finalSuffix secondWord =
      resultBase fixed K base finalSuffix (firstWord ++ secondWord) := by
  funext tape
  by_cases ho : tape = .inr Extra.reverseOutput
  · subst tape
    simp [resultBase, outputTapes, List.reverse_append, List.append_assoc]
  · by_cases he : tape = .inr Extra.endpoints
    · subst tape
      simp [resultBase, outputTapes]
    · simp [resultBase, outputTapes, ho, he]

theorem resultBase_counter (base : Tape fixed K → List Bool)
    (suffix word : List Bool) (count : Nat) :
    resultBase fixed K (PackingCountedProgram.counterTapes (.inr .edgeCounter) base count)
        suffix word =
      PackingCountedProgram.counterTapes (.inr .edgeCounter)
        (resultBase fixed K base suffix word) count := by
  funext tape
  by_cases hc : tape = .inr Extra.edgeCounter
  · subst tape
    simp [resultBase, outputTapes, PackingCountedProgram.counterTapes]
  · by_cases ho : tape = .inr Extra.reverseOutput
    · subst tape
      simp [resultBase, outputTapes, PackingCountedProgram.counterTapes]
    · by_cases he : tape = .inr Extra.endpoints
      · subst tape
        simp [resultBase, outputTapes, PackingCountedProgram.counterTapes]
      · simp [resultBase, outputTapes, PackingCountedProgram.counterTapes, hc, ho, he]

theorem resultBase_nil (base : Tape fixed K → List Bool)
    (empty : base (.inr .endpoints) = [false]) :
    resultBase fixed K base [false] [] = base := by
  simp only [resultBase, PackingChunkMachine.outputTapes_nil]
  rw [← empty, Function.update_eq_self]

def edgeTimePolynomial : Polynomial Nat :=
  prefixTimePolynomial + repeatTimePolynomial fixed K + cleanupTimePolynomial fixed K + 1

theorem edge_exec (x : GraphReductionInput) (e : x.graph.Edge)
    (base : Tape fixed K → List Bool) (state : State) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = true ::
      (BinaryEncoding.natBits (x.graph.left e).val ++
        (BinaryEncoding.natBits (x.graph.right e).val ++ suffix)))
    (decodeEmpty : base (.inr .decodeScratch) = [])
    (powerEmpty : base (.inr .powerCounter) = [])
    (repeatEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ (edgeTimePolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.edgeBody fixed K)
        ⟨state, tapes (Numerator fixed) denominator base (inputs fixed K x e.val)
          (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (resultBase fixed K base suffix (edgeWord fixed K x e))
            (inputs fixed K x (e.val + 1)) (preparedOther fixed K x)⟩ := by
  let decodedBase := Function.update base (.inr Extra.endpoints) suffix
  obtain ⟨n₁, b₁, r₁⟩ := prefix_exec fixed K x e base (inputs fixed K x e.val)
    suffix state sourceWord decodeEmpty powerEmpty
  have decodedRepeatEmpty : decodedBase (.inr .repetitionCounter) = [] := by
    simpa [decodedBase] using repeatEmpty
  obtain ⟨n₂, b₂, r₂⟩ := repeat_exec fixed K x e decodedBase
    (.arithmetic (BinaryAddMachine.clean ())) decodedRepeatEmpty
  obtain ⟨n₃, b₃, r₃⟩ := cleanup_exec fixed K x e
    (outputTapes (.inr .reverseOutput) decodedBase (edgeWord fixed K x e))
    (PackingCountedProgram.guardState none)
  have runs := (r₁.append r₂).append r₃
  refine ⟨(n₁ + n₂) + n₃ + 1, ?_, ?_⟩
  · simp only [edgeTimePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    omega
  · simpa only [GraphPackingProgram.edgeBody, prefixPhases, repeatPhases, cleanupPhases,
      List.cons_append, List.nil_append, decodedBase, resultBase, repeatFinalInputs]
      using runs.toExec

end BinPackingGap.GraphPackingJobs

end

end OAI
