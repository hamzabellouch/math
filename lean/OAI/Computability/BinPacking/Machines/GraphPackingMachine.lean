import OAI.Computability.BinPacking.Machines.GraphPackingGlobalExecution
import OAI.Computability.BinPacking.Machines.GraphPackingPreparation
import OAI.Computability.BinPacking.Machines.GraphPackingVerticesBound

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingFinish

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open BinPackingGames.Reduction.MachineTransfer

variable (fixed : InventoryData) (K : Nat)

def transfer : Code (K := Tape fixed K) (S := BinaryAddMachine.State Unit) :=
  .routine Unit inferInstance ()
    (fun _ => loopAt (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)

def resultTapes (base : Tape fixed K → List Bool) (word : List Bool) :
    Tape fixed K → List Bool :=
  Function.update (Function.update base (.inr .reverseOutput) [])
    (.inr .output) (word ++ [false])

@[simp] theorem resultTapes_output (base : Tape fixed K → List Bool) (word : List Bool) :
    resultTapes fixed K base word (.inr .output) = word ++ [false] := by
  simp [resultTapes]

@[simp] theorem resultTapes_reverse (base : Tape fixed K → List Bool) (word : List Bool) :
    resultTapes fixed K base word (.inr .reverseOutput) = [] := by
  simp [resultTapes]

theorem resultTapes_other (base : Tape fixed K → List Bool) (word : List Bool)
    (tape : Tape fixed K) (notReverse : tape ≠ .inr .reverseOutput)
    (notOutput : tape ≠ .inr .output) : resultTapes fixed K base word tape = base tape := by
  simp [resultTapes, notReverse, notOutput]

theorem transfer_exec (base : Tape fixed K → List Bool) (word : List Bool)
    (_reverseWord : base (.inr .reverseOutput) = word.reverse)
    (outputEmpty : base (.inr .output) = []) :
    Exec (transfer fixed K)
      ⟨BinaryAddMachine.clean (),
        Function.update base (.inr .reverseOutput) (false :: word.reverse)⟩
      (word.length + 2)
      ⟨BinaryAddMachine.clean (), resultTapes fixed K base word⟩ := by
  let pushed := Function.update base (.inr Extra.reverseOutput) (false :: word.reverse)
  have hreverse : pushed (.inr .reverseOutput) = false :: word.reverse := by simp [pushed]
  have run := transferAt_fromTapes
    (σ := (Unit × Bool) × Option Bool)
    (Γ := fun _ : Tape fixed K => Bool)
    (.inr Extra.reverseOutput) (.inr Extra.output) (by simp)
    id false () none
    (fun _ : Unit => loopAt (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)
    rfl pushed (((), false), none) none
  have after : tapesAt (.inr Extra.reverseOutput) (.inr Extra.output) pushed []
      ((pushed (.inr Extra.reverseOutput)).reverse.map id ++ pushed (.inr Extra.output)) =
      resultTapes fixed K base word := by
    simp [tapesAt, pushed, resultTapes, outputEmpty]
  rw [after, hreverse] at run
  have next_eq :
      nextAt (Γ := fun _ : Tape fixed K => Bool) (σ := (Unit × Bool) × Option Bool)
        (.inr Extra.output)
        (fun _ : Unit => loopAt (.inr Extra.reverseOutput) (.inr Extra.output)
          id false () none) =
      MachineComposition.advance
        (TM2.step (fun _ : Unit => loopAt
          (Γ := fun _ : Tape fixed K => Bool) (σ := (Unit × Bool) × Option Bool)
          (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)) := rfl
  rw [next_eq] at run
  unfold transfer
  apply Exec.routine (K := Tape fixed K) (S := BinaryAddMachine.State Unit) inferInstance ()
    (fun _ : Unit => loopAt (σ := (Unit × Bool) × Option Bool)
      (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)
  simpa only [List.length_cons, List.length_reverse, Nat.add_assoc, Nat.reduceAdd,
    BinaryAddMachine.State, BinaryAddMachine.clean, BinaryAddMachine.state, pushed] using run

theorem finish_exec (base : Tape fixed K → List Bool) (state : State) (word : List Bool)
    (reverseWord : base (.inr .reverseOutput) = word.reverse)
    (outputEmpty : base (.inr .output) = []) :
    Exec (GraphPackingProgram.finish fixed K) ⟨state, base⟩ (word.length + 5)
      ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes fixed K base word⟩ := by
  let push : Action (Tape fixed K) State :=
    .push (.inr .reverseOutput) (fun _ => false) .done
  let pushed := Function.update base (.inr Extra.reverseOutput) (false :: word.reverse)
  have first : Exec (.atom push) ⟨state, base⟩ 1 ⟨state, pushed⟩ := by
    simpa only [push, pushed, Action.eval, reverseWord] using Exec.atom push ⟨state, base⟩
  have second := PackingArithmeticProgram.exec (transfer fixed K) pushed
    (resultTapes fixed K base word) (word.length + 2) state
    (transfer_exec fixed K base word reverseWord outputEmpty)
  have third := Exec.atom (K := Tape fixed K) (S := State) .done
    ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes fixed K base word⟩
  have joined := Exec.seq first (Exec.seq second third)
  simpa only [GraphPackingProgram.finish, GraphPackingProgram.chain, transfer, push,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm, Action.eval] using joined

def rawProgram : MachineCanonicalOutput.Program (Tape fixed K)
    (GraphPackingProgram.code fixed K).Label State where
  input := .inr .input
  output := .inr .output
  main := (GraphPackingProgram.code fixed K).entry
  initial := .arithmetic (BinaryAddMachine.clean ())
  code := (GraphPackingProgram.code fixed K).instruction id none

theorem sourceMachine_eq : MachineCanonicalOutput.sourceMachine (rawProgram fixed K) =
    GraphPackingProgram.machine fixed K := rfl

def cleanupTapes : List (Tape fixed K) :=
  ((Finset.univ : Finset (Tape fixed K)).erase (.inr .output)).toList

theorem cleanup_complete (tape : Tape fixed K) :
    tape ∈ cleanupTapes fixed K ↔ tape ≠ (rawProgram fixed K).output := by
  simp [cleanupTapes, rawProgram]

def canonicalMachine : FinTM2 :=
  MachineCanonicalOutput.completedMachine (rawProgram fixed K) (cleanupTapes fixed K)

theorem canonical_finiteAlphabet :
    MachineFiniteAlphabet.FiniteAlphabet (canonicalMachine fixed K) :=
  MachineCanonicalOutput.finiteAlphabet (rawProgram fixed K) (cleanupTapes fixed K)

def canonicalTime (rawTime : Polynomial Nat) : Polynomial Nat :=
  MachineCanonicalOutput.completedTime (rawProgram fixed K) (cleanupTapes fixed K) rawTime

end BinPackingGap.GraphPackingFinish

namespace BinPackingGap.GraphPackingFixedParameters

def emptyGraph : GraphInput where
  n := 0
  edges := []
  ordered := by simp
  distinct := by simp

def fixedInventory (c : Nat) (ρ : ℝ) : InventoryData :=
  reductionInventory c ρ emptyGraph 0

theorem inventory_eq (c : Nat) (ρ : ℝ) (x : GraphReductionInput) :
    GraphPackingJobs.inventory (fixedInventory c ρ) (lossAllowance c) x =
      reductionInventory c ρ x.graph x.k := rfl

theorem binBound_eq_inventory (fixed : InventoryData) (K : Nat) (x : GraphReductionInput) :
    GraphPackingPreparation.binBound fixed K x = (GraphPackingJobs.inventory fixed K x).B := by
  exact congrFun (PackingSetupExpression.outputValues_eq_inventory
    (GraphPackingRegisters.parameters fixed K) (GraphPackingJobs.inventory fixed K x)
    rfl rfl rfl rfl) .bins

theorem binBound_eq_reduction (c : Nat) (ρ : ℝ) (x : GraphReductionInput) :
    GraphPackingPreparation.binBound (fixedInventory c ρ) (lossAllowance c) x =
      reductionBinBound c ρ x.graph x.k := by
  rw [binBound_eq_inventory, inventory_eq]
  rfl

theorem rawOutput_eq (c : Nat) (ρ : ℝ) (x : GraphReductionInput) :
    (GraphPackingJobs.inventory (fixedInventory c ρ) (lossAllowance c) x).rawOutput =
      graphPackingOutput c ρ x := by
  rw [inventory_eq]
  rfl

theorem outputBits_eq (c : Nat) (ρ : ℝ) (x : GraphReductionInput) :
    BinaryEncoding.natBits
        (GraphPackingPreparation.binBound (fixedInventory c ρ) (lossAllowance c) x) ++
      BinaryEncoding.rawInstanceBits
        (GraphPackingJobs.inventory (fixedInventory c ρ) (lossAllowance c) x).rawItemList =
      BinaryEncoding.rawReductionOutputBits (graphPackingOutput c ρ x) := by
  rw [binBound_eq_inventory]
  change BinaryEncoding.rawReductionOutputBits
    (GraphPackingJobs.inventory (fixedInventory c ρ) (lossAllowance c) x).rawOutput = _
  rw [rawOutput_eq]

end BinPackingGap.GraphPackingFixedParameters

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

def setupPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.setItem fixed K .edgePower 1,
    GraphPackingProgram.setItem fixed K .labelPower 0,
    GraphPackingProgram.setItem fixed K .repetitionOne 0,
    GraphPackingProgram.tally fixed K (.input .m) .edgeCounter]

def setupTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingCountedProgram.counterTapes (.inr .edgeCounter)
    (PackingMachineLayout.tapes (Numerator fixed) denominator
      (GraphPackingVertices.finalBase fixed K x) (inputs fixed K x 0)
      (preparedOther fixed K x)) x.graph.edges.length

private def resetInputs (x : GraphReductionInput) : Variable → Nat :=
  Function.update (Function.update (Function.update
    (GraphPackingVertices.finalInputs fixed K x) .edgePower 1) .labelPower 0) .repetitionOne 0

private theorem resetInputs_eq (x : GraphReductionInput) :
    resetInputs fixed K x = inputs fixed K x 0 := by
  have final_eq : GraphPackingVertices.finalInputs fixed K x =
      Function.update (GraphPackingVertices.startInputs fixed K x) .labelPower
        (3 ^ (x.graph.n + 1)) := by
    rw [GraphPackingVertices.startInputs_eq]
    simp only [GraphPackingVertices.finalInputs, PackingVertexLoop.vertexInput,
      Function.update_idem]
  unfold resetInputs
  rw [final_eq]
  funext a
  cases a <;> simp [GraphPackingVertices.startInputs, inputs, preparedInputs]

private theorem bounded_update {α : Type} [DecidableEq α]
    (values : α → Nat) (location : α) (value width : Nat)
    (h : ∀ a, (values a).size ≤ width) (hv : value.size ≤ width) :
    ∀ a, (Function.update values location value a).size ≤ width := by
  intro a
  by_cases ha : a = location
  · subst a
    simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne ha] using h a

theorem vertexFinalInputs_width (x : GraphReductionInput) :
    ∀ a, (GraphPackingVertices.finalInputs fixed K x a).size ≤
      GraphPackingWidths.width fixed K x + 2 := by
  have original := GraphPackingVertices.inputValues_width fixed K x
    (GraphPackingWidths.width fixed K x) (GraphPackingWidths.preparedInputs_width fixed K x)
  intro a
  by_cases ha : a = Variable.labelPower
  · subst a
    rw [GraphPackingVertices.final_labelPower]
    exact (GraphPackingWidths.vertex_power_width fixed K x (x.graph.n + 1) le_rfl).trans
      (by omega)
  · simpa only [GraphPackingVertices.finalInputs,
      PackingVertexLoop.vertexInput_other _ _ _ _ ha] using original a

private def setupValues (x : GraphReductionInput) : Register fixed K → Nat :=
  PackingMachineLayout.values (Numerator fixed) denominator (inputs fixed K x 0)
    (preparedOther fixed K x)

private theorem finalBase_edgeCounter (x : GraphReductionInput) :
    GraphPackingVertices.finalBase fixed K x (.inr .edgeCounter) = [] := by
  simp [GraphPackingVertices.finalBase, PackingItemBlockMachine.outputTapes,
    GraphPackingVertices.startBase, baseTapes]

private theorem tally_frame (x : GraphReductionInput) :
    registerTapes (slots fixed K)
      (Function.update (GraphPackingVertices.finalBase fixed K x) (.inr .edgeCounter)
        (List.replicate x.graph.edges.length true ++
          GraphPackingVertices.finalBase fixed K x (.inr .edgeCounter)))
      (setupValues fixed K x) = setupTapes fixed K x := by
  rw [finalBase_edgeCounter, List.append_nil]
  exact PackingRegisterFrame.external_update (slots fixed K)
    (GraphPackingVertices.finalBase fixed K x) (setupValues fixed K x) (.inr .edgeCounter)
    (GraphPackingTapeBlocks.slots_outside fixed K .edgeCounter)
    (List.replicate x.graph.edges.length true)

def setupSetPolynomial : Polynomial Nat :=
  PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 0 +
    PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0

def setupTimePolynomial : Polynomial Nat :=
  (setupSetPolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K + 2) +
    40 * (Polynomial.X + 1) ^ 3 + 1

private def setupBound (x : GraphReductionInput) : Nat :=
  (setupSetPolynomial fixed K).eval (GraphPackingWidths.width fixed K x + 2) +
    BinaryToTallyMachine.runtimeBound x.graph.edges.length + 1

private theorem setupBound_le (x : GraphReductionInput) :
    setupBound fixed K x ≤ (setupTimePolynomial fixed K).eval (graphBits x).length := by
  let size := (graphBits x).length
  have hm : x.graph.edges.length ≤ size := graph_edgeCount_le_bits x
  have hs : x.graph.edges.length.size ≤ size :=
    (nat_size_le_self _).trans hm
  have tally : BinaryToTallyMachine.runtimeBound x.graph.edges.length ≤
      40 * (size + 1) ^ 3 := by
    calc
      BinaryToTallyMachine.runtimeBound x.graph.edges.length =
          40 * (x.graph.edges.length + 1) * (x.graph.edges.length.size + 1) ^ 2 := rfl
      _ ≤ 40 * (size + 1) * (size + 1) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hm 1))
          (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2)
      _ = 40 * (size + 1) ^ 3 := by ring
  dsimp [size] at tally
  simp only [setupBound, setupTimePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, GraphPackingWidths.width]
  omega

theorem setup_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (setupTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (setupPhases fixed K)
        ⟨state, GraphPackingVertices.finalTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), setupTapes fixed K x⟩ := by
  let initial := GraphPackingVertices.finalInputs fixed K x
  let firstInput := Function.update initial .edgePower 1
  let secondInput := Function.update firstInput .labelPower 0
  let width := GraphPackingWidths.width fixed K x + 2
  have initialWidth : ∀ a, (initial a).size ≤ width := vertexFinalInputs_width fixed K x
  have otherWidth : ∀ a, (preparedOther fixed K x a).size ≤ width := by
    intro a
    exact (GraphPackingWidths.preparedOther_width fixed K x a).trans (by omega)
  have oneSize : (1 : Nat).size = 1 := by decide
  have zeroSize : (0 : Nat).size = 0 := by decide
  have firstWidth : ∀ a, (firstInput a).size ≤ width :=
    bounded_update initial .edgePower 1 width initialWidth (by dsimp [width]; omega)
  have secondWidth : ∀ a, (secondInput a).size ≤ width :=
    bounded_update firstInput .labelPower 0 width firstWidth (by dsimp [width]; omega)
  obtain ⟨firstSteps, firstBound, firstRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 (GraphPackingVertices.finalBase fixed K x)
    initial (preparedOther fixed K x) state width initialWidth otherWidth
  obtain ⟨secondSteps, secondBound, secondRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 0 (GraphPackingVertices.finalBase fixed K x)
    firstInput (preparedOther fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    width firstWidth otherWidth
  obtain ⟨thirdSteps, thirdBound, thirdRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0 (GraphPackingVertices.finalBase fixed K x)
    secondInput (preparedOther fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    width secondWidth otherWidth
  have thirdInput : Function.update secondInput .repetitionOne 0 = inputs fixed K x 0 :=
    resetInputs_eq fixed K x
  rw [thirdInput] at thirdRun
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec
    fixed K (.input .m) .edgeCounter (GraphPackingVertices.finalBase fixed K x)
    (setupValues fixed K x) (.arithmetic (BinaryAddMachine.clean ())) rfl rfl rfl
  have count : setupValues fixed K x (countRegister fixed K (.input .m)) =
      x.graph.edges.length := rfl
  rw [count] at tallyBound tallyRun
  rw [tally_frame] at tallyRun
  have phases : PhaseRuns (setupPhases fixed K)
      ⟨state, GraphPackingVertices.finalTapes fixed K x⟩
      (firstSteps + (secondSteps + (thirdSteps + tallySteps)))
      ⟨.arithmetic (BinaryAddMachine.clean ()), setupTapes fixed K x⟩ := by
    rw [GraphPackingVertices.finalTapes_eq_frame]
    exact .cons firstRun (.cons secondRun (.cons thirdRun (PhaseRuns.single tallyRun)))
  refine ⟨firstSteps + (secondSteps + (thirdSteps + tallySteps)),
    le_trans ?_ (setupBound_le fixed K x), phases⟩
  dsimp [width] at firstBound secondBound thirdBound
  simp only [setupBound, setupSetPolynomial, Polynomial.eval_add]
  omega

end

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

def emitted (x : GraphReductionInput) : List Bool :=
  PackingDescriptorExpression.rawRecords (PackingInventoryDescriptors.jobStream (inventory fixed K x))

def finalBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  resultBase fixed K (GraphPackingVertices.finalBase fixed K x) [false] (emitted fixed K x)

def finalTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  tapes (Numerator fixed) denominator (finalBase fixed K x)
    (inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)

@[simp] theorem finalBase_extra (x : GraphReductionInput) (e : Extra)
    (hne : e ≠ .endpoints) (hno : e ≠ .reverseOutput) (hni : e ≠ .input) :
    finalBase fixed K x (.inr e) = [] := by
  simp [finalBase, GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
    PackingItemBlockMachine.outputTapes, baseTapes, hne, hno, hni]

def timePolynomial : Polynomial Nat :=
  setupTimePolynomial fixed K + loopTimePolynomial fixed K + 1

theorem exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (timePolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.jobs fixed K)
        ⟨state, GraphPackingVertices.finalTapes fixed K x⟩ steps
        ⟨guardState none, finalTapes fixed K x⟩ := by
  obtain ⟨setupSteps, setupBound, setupRun⟩ := setup_exec fixed K x state
  have sourceWord : GraphPackingVertices.finalBase fixed K x (.inr .endpoints) =
      GraphFieldMachine.fieldBits .endpoints x := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  have decodeEmpty : GraphPackingVertices.finalBase fixed K x (.inr .decodeScratch) = [] := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  have powerEmpty : GraphPackingVertices.finalBase fixed K x (.inr .powerCounter) = [] := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  have repeatEmpty : GraphPackingVertices.finalBase fixed K x (.inr .repetitionCounter) = [] := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  obtain ⟨loopSteps, loopBound, loopRun⟩ := loop_exec fixed K x
    (GraphPackingVertices.finalBase fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    sourceWord decodeEmpty powerEmpty repeatEmpty
  have finalEmpty : finalTapes fixed K x (.inr .edgeCounter) = [] := by
    simp [finalTapes]
  have cleared : counterTapes (.inr Extra.edgeCounter) (finalTapes fixed K x) 0 =
      finalTapes fixed K x := by
    simp only [counterTapes, List.replicate_zero]
    rw [← finalEmpty, Function.update_eq_self]
  change Exec _ _ loopSteps
    ⟨guardState none, counterTapes (.inr .edgeCounter) (finalTapes fixed K x) 0⟩ at loopRun
  rw [cleared] at loopRun
  have runs := setupRun.append (PhaseRuns.single loopRun)
  refine ⟨setupSteps + loopSteps + 1, ?_, ?_⟩
  · simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    omega
  · simpa only [GraphPackingProgram.jobs, setupPhases, List.cons_append, List.nil_append]
      using runs.toExec

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingRun

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)
open PackingDescriptorExpression (rawRecords)
open PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

def globalWord (x : GraphReductionInput) : List Bool :=
  rawRecords (globalStream (GraphPackingJobs.inventory fixed K x))

def flagWord (x : GraphReductionInput) : List Bool :=
  rawRecords (flagStream (GraphPackingJobs.inventory fixed K x))

def afterGlobalBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (GraphPackingJobs.finalBase fixed K x) (globalWord fixed K x)

def beforeFinishBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (afterGlobalBase fixed K x) (flagWord fixed K x)

def beforeFinishTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  tapes (Numerator fixed) denominator (beforeFinishBase fixed K x)
    (GraphPackingJobs.inputs fixed K x 0) (preparedOther fixed K x)

def constructorWord (x : GraphReductionInput) : List Bool :=
  BinaryEncoding.natBits (binBound fixed K x) ++
    rawRecords (recipeStream (GraphPackingJobs.inventory fixed K x))

theorem beforeFinish_reverse (x : GraphReductionInput) :
    beforeFinishTapes fixed K x (.inr .reverseOutput) = (constructorWord fixed K x).reverse := by
  simp [beforeFinishTapes, beforeFinishBase, afterGlobalBase, GraphPackingJobs.finalBase,
    GraphPackingJobs.resultBase, GraphPackingVertices.finalBase,
    GraphPackingVertices.startBase, outputTapes, baseTapes, constructorWord,
    recipeStream, rawRecords, GraphPackingVertices.emitted, GraphPackingJobs.emitted,
    globalWord, flagWord, List.flatMap_append, List.reverse_append, List.append_assoc,
    GraphPackingVertices.data, GraphPackingJobs.inventory]

theorem beforeFinish_output_empty (x : GraphReductionInput) :
    beforeFinishTapes fixed K x (.inr .output) = [] := by
  simp [beforeFinishTapes, beforeFinishBase, afterGlobalBase, outputTapes]

theorem constructorWord_eq (x : GraphReductionInput) :
    constructorWord fixed K x ++ [false] =
      BinaryEncoding.rawReductionOutputBits (GraphPackingJobs.inventory fixed K x).rawOutput := by
  rw [PackingDescriptorExpression.reductionOutputBits_eq]
  simp only [constructorWord, recipeStream_eq_rawItemList, InventoryData.rawOutput,
    GraphPackingFixedParameters.binBound_eq_inventory]

def prefixPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.prepare fixed K, GraphPackingProgram.vertices fixed K,
    GraphPackingProgram.jobs fixed K, GraphPackingProgram.globals fixed K,
    GraphPackingProgram.flags fixed K]

def prefixProgram : GraphPackingProgram.Program fixed K :=
  GraphPackingProgram.chain fixed K (prefixPhases fixed K)

def prefixTimePolynomial : Polynomial Nat :=
  GraphPackingPreparation.timePolynomial fixed K +
    GraphPackingVerticesBound.polynomial fixed K + GraphPackingJobs.timePolynomial fixed K +
    GraphPackingGlobalRuntime.globalsPolynomial fixed K + GraphPackingGlobalRuntime.flagsPolynomial fixed K

theorem prefix_runs (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (prefixTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (prefixPhases fixed K)
        ⟨state, initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), beforeFinishTapes fixed K x⟩ := by
  obtain ⟨n₁, b₁, r₁⟩ := GraphPackingPreparation.prepare_exec fixed K x state
  obtain ⟨n₂, b₂, r₂⟩ := GraphPackingVerticesBound.exec fixed K x
    (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨n₃, b₃, r₃⟩ := GraphPackingJobs.exec fixed K x (PackingCountedProgram.guardState none)
  have jobPoolEmpty : GraphPackingJobs.finalBase fixed K x (.inr .poolCounter) = [] := by simp
  have jobEdgeEmpty : GraphPackingJobs.finalBase fixed K x (.inr .edgeCounter) = [] := by simp
  obtain ⟨n₄, b₄, r₄⟩ := GraphPackingGlobalExecution.globals_exec fixed K x
    (GraphPackingJobs.finalBase fixed K x) (PackingCountedProgram.guardState none)
    jobPoolEmpty jobEdgeEmpty
  have globalPoolEmpty : afterGlobalBase fixed K x (.inr .poolCounter) = [] := by
    simp [afterGlobalBase, outputTapes]
  obtain ⟨n₅, b₅, r₅⟩ := GraphPackingGlobalExecution.flags_exec fixed K x
    (afterGlobalBase fixed K x) (.arithmetic (BinaryAddMachine.clean ())) globalPoolEmpty
  have runs := PhaseRuns.cons r₁ (PhaseRuns.cons r₂
    (PhaseRuns.cons r₃ (PhaseRuns.cons r₄ (PhaseRuns.single r₅))))
  refine ⟨n₁ + (n₂ + (n₃ + (n₄ + n₅))), ?_, runs⟩
  simp only [prefixTimePolynomial, Polynomial.eval_add]
  omega

def prefixPushBound : Nat := Runtime.programPushBound
  ((prefixProgram fixed K).machine (.inr .input) (.inr .output)
    (.arithmetic (BinaryAddMachine.clean ())))

def wordTimePolynomial : Polynomial Nat :=
  (prefixTimePolynomial fixed K + 1) * Polynomial.C (prefixPushBound fixed K)

theorem constructorWord_length_le (x : GraphReductionInput) :
    (constructorWord fixed K x).length ≤
      (wordTimePolynomial fixed K).eval (graphBits x).length := by
  obtain ⟨steps, bound, runs⟩ := prefix_runs fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  have run : Exec (prefixProgram fixed K)
      ⟨.arithmetic (BinaryAddMachine.clean ()), initialTapes fixed K x⟩ (steps + 1)
      ⟨.arithmetic (BinaryAddMachine.clean ()), beforeFinishTapes fixed K x⟩ := runs.toExec
  have lengthBound := run.stack_length_le (.inr .input) (.inr .output)
    (.arithmetic (BinaryAddMachine.clean ())) (.inr .reverseOutput)
  change (beforeFinishTapes fixed K x (.inr .reverseOutput)).length ≤
    (initialTapes fixed K x (.inr .reverseOutput)).length +
      (steps + 1) * prefixPushBound fixed K at lengthBound
  rw [beforeFinish_reverse, List.length_reverse] at lengthBound
  have initialEmpty : initialTapes fixed K x (.inr .reverseOutput) = [] := rfl
  rw [initialEmpty, List.length_nil, Nat.zero_add] at lengthBound
  have times := Nat.mul_le_mul_right (prefixPushBound fixed K) (Nat.add_le_add_right bound 1)
  simp only [wordTimePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_C]
  exact lengthBound.trans times

def timePolynomial : Polynomial Nat :=
  prefixTimePolynomial fixed K + wordTimePolynomial fixed K + 6

def finalTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  GraphPackingFinish.resultTapes fixed K (beforeFinishTapes fixed K x) (constructorWord fixed K x)

theorem exec (x : GraphReductionInput) :
    ∃ steps ≤ (timePolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.code fixed K)
        ⟨.arithmetic (BinaryAddMachine.clean ()), initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), finalTapes fixed K x⟩ := by
  obtain ⟨prefixSteps, prefixBound, prefixRun⟩ := prefix_runs fixed K x
    (.arithmetic (BinaryAddMachine.clean ()))
  have finishRun := GraphPackingFinish.finish_exec fixed K (beforeFinishTapes fixed K x)
    (.arithmetic (BinaryAddMachine.clean ())) (constructorWord fixed K x)
    (beforeFinish_reverse fixed K x) (beforeFinish_output_empty fixed K x)
  have allRuns := prefixRun.append (PhaseRuns.single finishRun)
  refine ⟨prefixSteps + ((constructorWord fixed K x).length + 5) + 1, ?_, ?_⟩
  · have wordBound := constructorWord_length_le fixed K x
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
    omega
  · simpa only [GraphPackingProgram.code, prefixPhases, List.cons_append, List.nil_append,
      finalTapes] using allRuns.toExec

def terminalRun (x : GraphReductionInput) :
    MachineCanonicalOutput.TerminalRun (GraphPackingFinish.rawProgram fixed K)
      (graphBits x)
      (BinaryEncoding.rawReductionOutputBits (GraphPackingJobs.inventory fixed K x).rawOutput)
      ((timePolynomial fixed K).eval (graphBits x).length) := by
  classical
  let steps := Classical.choose (exec fixed K x)
  have bound := (Classical.choose_spec (exec fixed K x)).1
  have run := (Classical.choose_spec (exec fixed K x)).2
  refine {
    state := .arithmetic (BinaryAddMachine.clean ())
    tapes := finalTapes fixed K x
    execution := {
      steps := steps
      evals_in_steps := ?_
      steps_le_m := bound }
    output_eq := ?_ }
  · have initialEq : initList
        (MachineCanonicalOutput.sourceMachine (GraphPackingFinish.rawProgram fixed K)) (graphBits x) =
        (⟨some (GraphPackingProgram.code fixed K).entry,
          .arithmetic (BinaryAddMachine.clean ()), initialTapes fixed K x⟩ :
          (MachineCanonicalOutput.sourceMachine (GraphPackingFinish.rawProgram fixed K)).Cfg) := by
      unfold initList
      dsimp only [MachineCanonicalOutput.sourceMachine, GraphPackingFinish.rawProgram]
      congr 1
      funext tape
      cases tape with
      | inl tape => simp [initialTapes]
      | inr extra =>
          cases extra <;> simp [initialTapes]
          rfl
    change (MachineComposition.advance
      (TM2.step ((GraphPackingProgram.code fixed K).instruction id none)))^[steps]
      (some (initList
        (MachineCanonicalOutput.sourceMachine (GraphPackingFinish.rawProgram fixed K)) (graphBits x))) =
      some ⟨none, .arithmetic (BinaryAddMachine.clean ()), finalTapes fixed K x⟩
    rw [initialEq]
    exact run.trace ((GraphPackingProgram.code fixed K).instruction id none) id none (fun _ => rfl)
  · change finalTapes fixed K x (.inr .output) = _
    rw [finalTapes, GraphPackingFinish.resultTapes_output, constructorWord_eq]

end BinPackingGap.GraphPackingRun

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

def graphPackingComputation (c : Nat) (ρ : ℝ) :
    TM2ComputableInPolyTime graphBits BinaryEncoding.rawReductionOutputBits
      (graphPackingOutput c ρ) :=
  MachineCanonicalOutput.computableInPolyTime
    (GraphPackingFinish.rawProgram (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    (GraphPackingFinish.cleanupTapes (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    (GraphPackingFinish.cleanup_complete (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    graphBits BinaryEncoding.rawReductionOutputBits (graphPackingOutput c ρ)
    (GraphPackingRun.timePolynomial (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    (fun x => by
      simpa only [GraphPackingFixedParameters.rawOutput_eq] using
        GraphPackingRun.terminalRun (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c) x)

theorem graphPackingComputation_finiteAlphabet (c : Nat) (ρ : ℝ) :
    MachineFiniteAlphabet.FiniteAlphabet (graphPackingComputation c ρ).tm :=
  GraphPackingFinish.canonical_finiteAlphabet
    (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c)

end BinPackingGap

end

end OAI
