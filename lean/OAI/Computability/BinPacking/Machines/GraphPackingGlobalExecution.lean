import Mathlib.Data.List.FinRange
import OAI.Computability.BinPacking.Machines.GraphPackingJobEdge
import OAI.Computability.BinPacking.Machines.GraphPackingStockStreams

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPoolExec

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout PackingItemExpression PackingInventoryDescriptors
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes)

section Layout

variable {δ α β ε : Type} [DecidableEq δ] [DecidableEq α]
variable [DecidableEq β] [DecidableEq ε]

theorem layout_external_update (num : δ → Expr α) (den : Expr α)
    (base : Tape num den β ε → List Bool) (input : α → Nat) (other : β → Nat)
    (external : ε) (word : List Bool) :
    tapes num den (Function.update base (.inr external) word) input other =
      Function.update (tapes num den base input other) (.inr external) word := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

theorem layout_output (num : δ → Expr α) (den : Expr α)
    (base : Tape num den β ε → List Bool) (input : α → Nat) (other : β → Nat)
    (output : ε) (word : List Bool) :
    outputTapes (.inr output) (tapes num den base input other) word =
      tapes num den (outputTapes (.inr output) base word) input other := by
  unfold outputTapes
  rw [tapes_extra, layout_external_update]

theorem layout_counter (num : δ → Expr α) (den : Expr α)
    (base : Tape num den β ε → List Bool) (input : α → Nat) (other : β → Nat)
    (counter : ε) (n : Nat) :
    counterTapes (.inr counter) (tapes num den base input other) n =
      tapes num den (counterTapes (.inr counter) base n) input other := by
  exact (layout_external_update num den base input other counter
    (List.replicate n true)).symm

end Layout

open GraphPackingRegisters

variable (fixed : InventoryData) (K : Nat)

def poolWord (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (input : Variable → Nat) (other : Other fixed K → Nat) : List Bool :=
  PackingConstantPool.repeatRecords
    (PackingChunkMachine.records (Numerator fixed) denominator (fun _ => input) [descriptor])
    (other (GraphPackingProgram.otherSetup fixed K stock))

def poolBudget (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (other : Other fixed K → Nat) (width : Nat) : Nat :=
  let n := other (GraphPackingProgram.otherSetup fixed K stock)
  BinaryToTallyMachine.runtimeBound n +
    n * ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).eval width + 2) + 3

theorem pool_exec (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (base : GraphPackingRegisters.Tape fixed K → List Bool)
    (input : Variable → Nat) (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hwidth : ∀ a, (input a).size ≤ width) :
    ∃ steps ≤ poolBudget fixed K stock descriptor other width,
      Exec (GraphPackingProgram.pool fixed K stock descriptor)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (poolWord fixed K stock descriptor input other)) input other⟩ := by
  let vals := PackingMachineLayout.values (Numerator fixed) denominator input other
  let n := other (GraphPackingProgram.otherSetup fixed K stock)
  let filledBase := counterTapes (.inr Extra.poolCounter) base n
  let filled := tapes (Numerator fixed) denominator filledBase input other
  have sourceValue : vals (countRegister fixed K (.output stock)) = n := rfl
  have workCounter : vals (work fixed K .counter) = 0 := counterZero
  have workOne : vals (work fixed K .one) = 0 := oneZero
  have workTemporary : vals (work fixed K .temporary) = 0 := temporaryZero
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec fixed K
    (.output stock) .poolCounter base vals state workCounter workOne workTemporary
  simp only [sourceValue] at tallyBound
  have tallyRun' : Exec (GraphPackingProgram.tally fixed K (.output stock) .poolCounter)
      ⟨state, tapes (Numerator fixed) denominator base input other⟩ tallySteps
      ⟨.arithmetic (BinaryAddMachine.clean ()), filled⟩ := by
    simp only [sourceValue, poolEmpty, List.append_nil] at tallyRun
    simpa only [filled, filledBase, counterTapes, PackingMachineLayout.tapes,
      GraphPackingRegisters.slots, vals] using tallyRun
  have counterWord : filled (.inr .poolCounter) = List.replicate n true := by
    simp [filled, filledBase, counterTapes]
  have shape : ∀ d ∈ [descriptor],
      registerTapes (itemSlots (Numerator fixed) denominator d) filled
        (PairExpressionCompiler.initial (Numerator fixed d) denominator input) = filled := by
    intro d _
    exact item_shape (Numerator fixed) denominator filledBase input other d
  obtain ⟨poolSteps, poolBound, poolRun⟩ := PackingConstantPool.exec_from_tapes
    (Numerator fixed) denominator (itemSlots (Numerator fixed) denominator)
    (.inr Extra.reverseOutput) (.inr Extra.poolCounter)
    (by
      intro h
      have impossible : Extra.poolCounter = Extra.reverseOutput := Sum.inr.inj h
      cases impossible)
    (fun d i => itemSlots_outside (Other := Other fixed K)
      (Numerator fixed) denominator d Extra.reverseOutput i)
    (fun d i => itemSlots_outside (Other := Other fixed K)
      (Numerator fixed) denominator d Extra.poolCounter i)
    [descriptor] filled (fun _ => input) (.arithmetic (BinaryAddMachine.clean ())) width n
    counterWord shape (by intro _ _ a; exact hwidth a)
  have clearCounter : counterTapes (.inr Extra.poolCounter) filledBase 0 = base := by
    simp only [filledBase, counterTapes, List.replicate_zero, Function.update_idem]
    rw [← poolEmpty, Function.update_eq_self]
  have finalFrame : outputTapes (.inr Extra.reverseOutput)
      (counterTapes (.inr Extra.poolCounter) filled 0)
      (PackingConstantPool.repeatRecords
        (PackingChunkMachine.records (Numerator fixed) denominator (fun _ => input) [descriptor]) n) =
      tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base
          (poolWord fixed K stock descriptor input other)) input other := by
    change outputTapes (.inr Extra.reverseOutput)
      (counterTapes (.inr Extra.poolCounter)
        (tapes (Numerator fixed) denominator filledBase input other) 0) _ = _
    rw [layout_counter, clearCounter, layout_output]
    rfl
  rw [finalFrame] at poolRun
  have phases : GraphPackingProgram.PhaseRuns
      [GraphPackingProgram.tally fixed K (.output stock) .poolCounter,
        PackingConstantPool.code (Numerator fixed) denominator
          (itemSlots (Numerator fixed) denominator)
          (.inr .reverseOutput) (.inr .poolCounter) [descriptor]]
      ⟨state, tapes (Numerator fixed) denominator base input other⟩
      (tallySteps + poolSteps)
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator
          (outputTapes (.inr .reverseOutput) base
            (poolWord fixed K stock descriptor input other)) input other⟩ :=
    .cons tallyRun' (GraphPackingProgram.PhaseRuns.single poolRun)
  refine ⟨tallySteps + poolSteps + 1, ?_, ?_⟩
  · change tallySteps + poolSteps + 1 ≤ BinaryToTallyMachine.runtimeBound n +
      n * ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).eval width + 2) + 3
    omega
  · simpa only [GraphPackingProgram.pool] using phases.toExec

end BinPackingGap.GraphPackingPoolExec

namespace BinPackingGap.GraphPackingGlobalLoop

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

def radix (other : Other fixed K → Nat) : Nat :=
  other (otherSetup fixed K .base)

def edgeInput (input : Variable → Nat) (other : Other fixed K → Nat) (edge : Nat) :
    Variable → Nat := Function.update input .edgePower (radix fixed K other ^ edge)

@[simp] theorem edgeInput_power (input : Variable → Nat) (other : Other fixed K → Nat)
    (edge : Nat) : edgeInput fixed K input other edge .edgePower = radix fixed K other ^ edge := by
  simp [edgeInput]

theorem edgeInput_update (input : Variable → Nat) (other : Other fixed K → Nat) (edge : Nat) :
    Function.update (edgeInput fixed K input other edge) .edgePower
      (radix fixed K other * edgeInput fixed K input other edge .edgePower) =
      edgeInput fixed K input other (edge + 1) := by
  rw [edgeInput_power]
  simp only [edgeInput, Function.update_idem, Nat.pow_succ, Nat.mul_comm]

def aggregateWidth (other : Other fixed K → Nat) (inputWidth start count : Nat) : Nat :=
  inputWidth + (start + count) * (radix fixed K other).size + 1

theorem edgeInput_size_le (input : Variable → Nat) (other : Other fixed K → Nat)
    (inputWidth start count edge : Nat) (initial : ∀ a, (input a).size ≤ inputWidth)
    (he : edge ≤ start + count) :
    ∀ a, (edgeInput fixed K input other edge a).size ≤
      aggregateWidth fixed K other inputWidth start count := by
  intro a
  by_cases h : a = .edgePower
  · subst a
    rw [edgeInput_power]
    have hp := nat_size_pow_le (radix fixed K other) edge
    have hm := Nat.mul_le_mul_right (radix fixed K other).size he
    unfold aggregateWidth
    omega
  · have hi := initial a
    simp only [edgeInput, Function.update_of_ne h]
    unfold aggregateWidth
    omega

def edgeWord (input : Variable → Nat) (other : Other fixed K → Nat) : List Bool :=
  poolWord fixed K .edgeStock (.w, .globalEdge true) input other ++
  poolWord fixed K .edgeStock (.w, .globalEdge false) input other

def bodyBudget (other : Other fixed K → Nat) (width : Nat) : Nat :=
  poolBudget fixed K .edgeStock (.w, .globalEdge true) other width +
  poolBudget fixed K .edgeStock (.w, .globalEdge false) other width +
  64 * ((radix fixed K other).size + width + 1) ^ 2 + 1

theorem body_exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) :
    ∃ steps ≤ bodyBudget fixed K other width,
      Exec (globalEdgeBody fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (edgeWord fixed K input other))
            (Function.update input .edgePower (radix fixed K other * input .edgePower)) other⟩ := by
  let first := poolWord fixed K .edgeStock (.w, .globalEdge true) input other
  let second := poolWord fixed K .edgeStock (.w, .globalEdge false) input other
  let middle := outputTapes (.inr .reverseOutput) base first
  obtain ⟨n₁, b₁, r₁⟩ := pool_exec fixed K .edgeStock (.w, .globalEdge true)
    base input other state width counterZero oneZero temporaryZero poolEmpty hi
  have emptyMiddle : middle (.inr .poolCounter) = [] := by
    simpa [middle, outputTapes] using poolEmpty
  obtain ⟨n₂, b₂, r₂⟩ := pool_exec fixed K .edgeStock (.w, .globalEdge false)
    middle input other (.arithmetic (BinaryAddMachine.clean ())) width
    counterZero oneZero temporaryZero emptyMiddle hi
  obtain ⟨n₃, b₃, r₃⟩ := PackingVertexUpdate.general_exec
    (Numerator fixed) denominator .edgePower (otherSetup fixed K .base)
    (.inr Work.temporary) (by simp [otherSetup]) .multiply
    (outputTapes (.inr .reverseOutput) middle second) input other temporaryZero
    (.arithmetic (BinaryAddMachine.clean ()))
  have operationMultiply (a b : Nat) :
      PackingRegisterUpdate.operation .multiply a b = a * b := rfl
  have runs := PhaseRuns.cons r₁ (PhaseRuns.cons r₂ (PhaseRuns.single r₃))
  refine ⟨n₁ + (n₂ + n₃) + 1, ?_, ?_⟩
  · have square := Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add_left (hi .edgePower) (radix fixed K other).size) 1) 2
    have ub := b₃.trans (Nat.mul_le_mul_left 64 square)
    unfold bodyBudget
    omega
  · simpa only [globalEdgeBody, incrementEdge, operationMultiply,
      radix, middle, first, second, edgeWord, PackingChunkMachine.outputTapes_append]
      using runs.toExec

def stream (input : Variable → Nat) (other : Other fixed K → Nat) (start : Nat) :
    Nat → List Bool
  | 0 => []
  | count + 1 => edgeWord fixed K (edgeInput fixed K input other start) other ++
      stream input other (start + 1) count

private theorem layout_counter (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (count : Nat) :
    tapes (Numerator fixed) denominator (counterTapes (.inr .edgeCounter) base count) input other =
      counterTapes (.inr .edgeCounter) (tapes (Numerator fixed) denominator base input other) count := by
  exact layout_external_update (Numerator fixed) denominator base input other .edgeCounter (List.replicate count true)

private theorem exec_bounded (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (start count width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ edge, start ≤ edge → edge < start + count →
      ∀ a, (edgeInput fixed K input other edge a).size ≤ width) :
    ∃ steps ≤ count * (bodyBudget fixed K other width + 1) + 1,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (stream fixed K input other start count))
            (edgeInput fixed K input other (start + count)) other) 0⟩ := by
  induction count generalizing base start state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
          ⟨state, counterTapes (.inr .edgeCounter)
            (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        stream, PackingChunkMachine.outputTapes_nil, Nat.add_zero] using
        (Exec.loop_false (a := globalEdgeBody fixed K) stop)
  | succ count ih =>
      let word := edgeWord fixed K (edgeInput fixed K input other start) other
      have poolEmpty' : counterTapes (.inr .edgeCounter) base count (.inr .poolCounter) = [] := by
        simpa [counterTapes] using poolEmpty
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := body_exec fixed K
        (counterTapes (.inr .edgeCounter) base count) (edgeInput fixed K input other start)
        other (guardState (some true)) width counterZero oneZero temporaryZero poolEmpty'
        (hi start (by omega) (by omega))
      rw [edgeInput_update, layout_counter,
        PackingConstantPool.output_counter_comm _ _ (by simp), layout_counter] at bodyRun
      have poolEmpty'' : outputTapes (.inr .reverseOutput) base word (.inr .poolCounter) = [] := by
        simpa [outputTapes] using poolEmpty
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih
        (base := outputTapes (.inr .reverseOutput) base word)
        (state := .arithmetic (BinaryAddMachine.clean ())) (start := start + 1)
        poolEmpty'' (fun edge lower upper => hi edge (by omega) (by omega))
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other)
                (count + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyRun' : Exec (globalEdgeBody fixed K)
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other)
                (count + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
              (tapes (Numerator fixed) denominator (outputTapes (.inr .reverseOutput) base word)
                (edgeInput fixed K input other (start + 1)) other) count⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun
        have combined := Exec.loop_true more bodyRun' tailRun
        simpa only [PackingCountedProgram.loop, word, stream,
          PackingChunkMachine.outputTapes_append, Nat.add_assoc, Nat.add_comm 1 count] using combined

theorem exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (start count inputWidth : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ inputWidth) :
    ∃ steps ≤ count * (bodyBudget fixed K other
        (aggregateWidth fixed K other inputWidth start count) + 1) + 1,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (stream fixed K input other start count))
            (edgeInput fixed K input other (start + count)) other) 0⟩ := by
  exact exec_bounded fixed K base input other state start count _ counterZero oneZero temporaryZero
    poolEmpty (fun edge _ upper => edgeInput_size_le fixed K input other inputWidth start count
      edge hi (Nat.le_of_lt upper))

end BinPackingGap.GraphPackingGlobalLoop

namespace BinPackingGap.GraphPackingGlobalPhases

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

abbrev Pool := PackingSetupExpression.Output × PackingInventoryDescriptors.ItemDescriptor fixed

def poolListWord (pools : List (Pool fixed)) (input : Variable → Nat)
    (other : Other fixed K → Nat) : List Bool :=
  pools.flatMap (fun pool => poolWord fixed K pool.1 pool.2 input other)

def poolListBudget (pools : List (Pool fixed)) (other : Other fixed K → Nat)
    (width : Nat) : Nat :=
  (pools.map (fun pool => poolBudget fixed K pool.1 pool.2 other width)).sum

theorem pool_runs (pools : List (Pool fixed)) (base : GraphPackingRegisters.Tape fixed K → List Bool)
    (input : Variable → Nat) (other : Other fixed K → Nat) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) :
    ∃ steps ≤ poolListBudget fixed K pools other width,
      PhaseRuns (pools.map (fun p => GraphPackingProgram.pool fixed K p.1 p.2))
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (poolListWord fixed K pools input other))
            input other⟩ := by
  induction pools generalizing base with
  | nil =>
      refine ⟨0, by simp [poolListBudget], ?_⟩
      simpa only [List.map_nil, poolListWord, List.flatMap_nil,
        PackingChunkMachine.outputTapes_nil] using
        (PhaseRuns.nil ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator base input other⟩)
  | cons p rest ih =>
      let word := poolWord fixed K p.1 p.2 input other
      let middle := outputTapes (.inr .reverseOutput) base word
      obtain ⟨headSteps, headBound, headRun⟩ := pool_exec fixed K p.1 p.2 base input other
        (.arithmetic (BinaryAddMachine.clean ())) width counterZero oneZero temporaryZero poolEmpty hi
      have poolEmpty' : middle (.inr .poolCounter) = [] := by
        simpa [middle, outputTapes] using poolEmpty
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih middle poolEmpty'
      refine ⟨headSteps + tailSteps, ?_, ?_⟩
      · simpa only [poolListBudget, List.map_cons, List.sum_cons] using
          Nat.add_le_add headBound tailBound
      · simpa only [List.map_cons, poolListWord, List.flatMap_cons, middle, word,
          PackingChunkMachine.outputTapes_append] using PhaseRuns.cons headRun tailRun

def unitPools : List (Pool fixed) :=
  [(.upOne, (.up, .globalUnit true)), (.upZero, (.up, .globalUnit false)),
   (.umOne, (.um, .globalUnit true)), (.umZero, (.um, .globalUnit false))]

def flagPools : List (Pool fixed) :=
  [(.treeFlags, (.ft, .zero)), (.jobFlags, (.fm, .zero)), (.jobFlags, (.fg, .zero))]

private theorem update_width (input : Variable → Nat) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (destination : Variable) (constant : Nat)
    (hc : constant.size ≤ width) :
    ∀ a, (Function.update input destination constant a).size ≤ width := by
  intro a
  by_cases h : a = destination
  · subst a
    simpa only [Function.update_self] using hc
  · simpa only [Function.update_of_ne h] using hi a

def flagInput (input : Variable → Nat) : Variable → Nat := Function.update input .edgePower 1

def flagsBudget (other : Other fixed K → Nat) (width : Nat) : Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).eval (width + 1) +
  poolListBudget fixed K (flagPools fixed) other (width + 1) + 1

theorem flags_exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ flagsBudget fixed K other width,
      Exec (GraphPackingProgram.flags fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (poolListWord fixed K (flagPools fixed) (flagInput input) other))
            (flagInput input) other⟩ := by
  have hi' : ∀ a, (input a).size ≤ width + 1 := fun a => (hi a).trans (Nat.le_succ _)
  have ho' : ∀ a, (other a).size ≤ width + 1 := fun a => (ho a).trans (Nat.le_succ _)
  obtain ⟨resetSteps, resetBound, resetRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 base input other state (width + 1) hi' ho'
  have afterWidth : ∀ a, (flagInput input a).size ≤ width + 1 :=
    update_width input (width + 1) hi' .edgePower 1 (by simp [Nat.size_one])
  obtain ⟨poolSteps, poolBound, poolRun⟩ := pool_runs fixed K (flagPools fixed)
    base (flagInput input) other (width + 1) counterZero oneZero temporaryZero poolEmpty afterWidth
  refine ⟨resetSteps + poolSteps + 1, ?_, ?_⟩
  · unfold flagsBudget
    omega
  · simpa only [GraphPackingProgram.flags, GraphPackingProgram.setItem, flagPools,
      List.map_cons, List.map_nil, flagInput] using (PhaseRuns.cons resetRun poolRun).toExec

def unitInput (input : Variable → Nat) : Variable → Nat :=
  Function.update (Function.update (Function.update input .labelPower 0) .repetitionOne 0) .edgePower 1

def globalCount (other : Other fixed K → Nat) : Nat :=
  other (.inl (PackingSetupMachine.input (parameters fixed K) .m))

def globalsWord (input : Variable → Nat) (other : Other fixed K → Nat) : List Bool :=
  poolListWord fixed K (unitPools fixed) (unitInput input) other ++
  GraphPackingGlobalLoop.stream fixed K (unitInput input) other 0 (globalCount fixed K other)

def globalsInput (input : Variable → Nat) (other : Other fixed K → Nat) : Variable → Nat :=
  GraphPackingGlobalLoop.edgeInput fixed K (unitInput input) other (globalCount fixed K other)

def resetBudget (width : Nat) : Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .labelPower 0).eval (width + 1) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .repetitionOne 0).eval (width + 1) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).eval (width + 1)

def globalsBudget (other : Other fixed K → Nat) (width : Nat) : Nat :=
  resetBudget fixed K width + poolListBudget fixed K (unitPools fixed) other (width + 1) +
  BinaryToTallyMachine.runtimeBound (globalCount fixed K other) +
  globalCount fixed K other * (GraphPackingGlobalLoop.bodyBudget fixed K other
    (GraphPackingGlobalLoop.aggregateWidth fixed K other (width + 1) 0
      (globalCount fixed K other)) + 1) + 3

theorem globals_exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (edgeEmpty : base (.inr .edgeCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ globalsBudget fixed K other width,
      Exec (GraphPackingProgram.globals fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other))
            (globalsInput fixed K input other) other⟩ := by
  let input₁ := Function.update input .labelPower 0
  let input₂ := Function.update input₁ .repetitionOne 0
  let finalInput := unitInput input
  have hi' : ∀ a, (input a).size ≤ width + 1 := fun a => (hi a).trans (Nat.le_succ _)
  have ho' : ∀ a, (other a).size ≤ width + 1 := fun a => (ho a).trans (Nat.le_succ _)
  have hi₁ : ∀ a, (input₁ a).size ≤ width + 1 := update_width input _ hi' .labelPower 0 (by simp)
  have hi₂ : ∀ a, (input₂ a).size ≤ width + 1 := update_width input₁ _ hi₁ .repetitionOne 0 (by simp)
  have hi₃ : ∀ a, (finalInput a).size ≤ width + 1 :=
    update_width input₂ _ hi₂ .edgePower 1 (by simp [Nat.size_one])
  obtain ⟨n₁, b₁, r₁⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 0 base input other state (width + 1) hi' ho'
  obtain ⟨n₂, b₂, r₂⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0 base input₁ other
    (.arithmetic (BinaryAddMachine.clean ())) (width + 1) hi₁ ho'
  obtain ⟨n₃, b₃, r₃⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 base input₂ other
    (.arithmetic (BinaryAddMachine.clean ())) (width + 1) hi₂ ho'
  let unitWord := poolListWord fixed K (unitPools fixed) finalInput other
  let middle := outputTapes (.inr .reverseOutput) base unitWord
  obtain ⟨np, bp, rp⟩ := pool_runs fixed K (unitPools fixed) base finalInput other (width + 1)
    counterZero oneZero temporaryZero poolEmpty hi₃
  let vals := values (Numerator fixed) denominator finalInput other
  obtain ⟨nt, bt, rt⟩ := GraphPackingTapeBlocks.tally_exec fixed K (.input .m) .edgeCounter
    middle vals (.arithmetic (BinaryAddMachine.clean ())) counterZero oneZero temporaryZero
  have middleEdge : middle (.inr .edgeCounter) = [] := by
    simpa [middle, outputTapes] using edgeEmpty
  have middlePool : middle (.inr .poolCounter) = [] := by
    simpa [middle, outputTapes] using poolEmpty
  have atZero : GraphPackingGlobalLoop.edgeInput fixed K finalInput other 0 = finalInput := by
    unfold GraphPackingGlobalLoop.edgeInput
    simp only [Nat.pow_zero]
    change Function.update (Function.update input₂ .edgePower 1) .edgePower 1 = _
    rw [Function.update_idem]
    rfl
  have countValue : vals (countRegister fixed K (.input .m)) = globalCount fixed K other := rfl
  have rt' : Exec (tally fixed K (.input .m) .edgeCounter)
      ⟨.arithmetic (BinaryAddMachine.clean ()), tapes (Numerator fixed) denominator middle finalInput other⟩ nt
      ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
        (tapes (Numerator fixed) denominator middle finalInput other) (globalCount fixed K other)⟩ := by
    rw [GraphPackingPoolExec.layout_counter]
    simp only [countValue, middleEdge, List.append_nil] at rt
    simpa only [PackingMachineLayout.tapes, GraphPackingRegisters.slots, vals,
      counterTapes] using rt
  obtain ⟨nl, bl, rl⟩ := GraphPackingGlobalLoop.exec fixed K middle finalInput other
    (.arithmetic (BinaryAddMachine.clean ())) 0 (globalCount fixed K other) (width + 1)
    counterZero oneZero temporaryZero middlePool hi₃
  rw [atZero] at rl
  have finalCounter : counterTapes (.inr .edgeCounter)
      (tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) middle
          (GraphPackingGlobalLoop.stream fixed K finalInput other 0 (globalCount fixed K other)))
        (globalsInput fixed K input other) other) 0 =
      tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other))
        (globalsInput fixed K input other) other := by
    have words : outputTapes (.inr .reverseOutput) middle
        (GraphPackingGlobalLoop.stream fixed K finalInput other 0 (globalCount fixed K other)) =
        outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other) := by
      dsimp only [middle, unitWord, globalsWord, finalInput]
      rw [PackingChunkMachine.outputTapes_append]
    rw [words]
    unfold counterTapes
    rw [List.replicate_zero, Function.update_eq_self_iff]
    simp [outputTapes, edgeEmpty]
  have atCount : GraphPackingGlobalLoop.edgeInput fixed K finalInput other
      (globalCount fixed K other) = globalsInput fixed K input other := rfl
  have rl' : Exec (PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K))
      ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
        (tapes (Numerator fixed) denominator middle finalInput other) (globalCount fixed K other)⟩ nl
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator
          (outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other))
          (globalsInput fixed K input other) other⟩ := by
    rw [Nat.zero_add, atCount, finalCounter] at rl
    simpa only [guardState, BinaryAddMachine.clean, BinaryAddMachine.state] using rl
  have runs := PhaseRuns.cons r₁ (PhaseRuns.cons r₂ (PhaseRuns.cons r₃
    (rp.append (PhaseRuns.cons rt' (PhaseRuns.single rl')))))
  refine ⟨n₁ + (n₂ + (n₃ + (np + (nt + nl)))) + 1, ?_, ?_⟩
  · rw [countValue] at bt
    unfold globalsBudget resetBudget
    omega
  · simpa only [GraphPackingProgram.globals, GraphPackingProgram.setItem, unitPools,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      using runs.toExec

end BinPackingGap.GraphPackingGlobalPhases

namespace BinPackingGap.GraphPackingGlobalLoop

open GraphPackingRegisters
open PackingItemExpression (Variable)

theorem stream_eq_finRange (fixed : InventoryData) (K : Nat)
    (input : Variable → Nat) (other : Other fixed K → Nat) (start count : Nat) :
    stream fixed K input other start count =
      (List.finRange count).flatMap (fun j =>
        edgeWord fixed K (edgeInput fixed K input other (start + j.val)) other) := by
  induction count generalizing start with
  | zero => simp [stream]
  | succ count ih =>
      rw [stream, ih, List.finRange_succ, List.flatMap_cons, List.flatMap_map]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
      congr 1
      apply congrArg (fun f => (List.finRange count).flatMap f)
      funext j
      have index : start + 1 + j.val = start + (j.val + 1) := by omega
      rw [index]

end BinPackingGap.GraphPackingGlobalLoop

namespace BinPackingGap.GraphPackingJobs

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open GraphPackingPoolExec (layout_counter)

variable (fixed : InventoryData) (K : Nat)

theorem loop_exec_list (x : GraphReductionInput) (es : List x.graph.Edge)
    (base : Tape fixed K → List Bool) (start : Nat) (state : State)
    (indices : es.map Fin.val = List.range' start es.length)
    (sourceWord : base (.inr .endpoints) = edgeFields x es)
    (decodeEmpty : base (.inr .decodeScratch) = [])
    (powerEmpty : base (.inr .powerCounter) = [])
    (repeatEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ es.length * ((edgeTimePolynomial fixed K).eval (graphBits x).length + 1) + 1,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (GraphPackingProgram.edgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (inputs fixed K x start)
            (preparedOther fixed K x)) es.length⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (resultBase fixed K base [false] (edgeWords fixed K x es))
            (inputs fixed K x (start + es.length)) (preparedOther fixed K x)) 0⟩ := by
  induction es generalizing base start state with
  | nil =>
      have endpointNil : base (.inr .endpoints) = [false] := by
        simpa [edgeFields, BinaryEncoding.listBits] using sourceWord
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more
          ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
            ⟨state, counterTapes (.inr .edgeCounter)
              (tapes (Numerator fixed) denominator base (inputs fixed K x start)
                (preparedOther fixed K x)) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        edgeWords, List.flatMap_nil, List.length_nil, Nat.add_zero,
        resultBase_nil fixed K base endpointNil] using
        (Exec.loop_false (a := GraphPackingProgram.edgeBody fixed K) stop)
  | cons e es ih =>
      obtain ⟨headIndex, tailIndices⟩ := contiguous_cons e es start indices
      let currentBase := counterTapes (.inr Extra.edgeCounter) base es.length
      let middleBase := resultBase fixed K base (edgeFields x es) (edgeWord fixed K x e)
      have currentWord : currentBase (.inr .endpoints) = true ::
          (BinaryEncoding.natBits (x.graph.left e).val ++
            (BinaryEncoding.natBits (x.graph.right e).val ++ edgeFields x es)) := by
        simpa [currentBase, counterTapes, edgeFields, BinaryEncoding.listBits,
          List.append_assoc] using sourceWord
      have currentDecode : currentBase (.inr .decodeScratch) = [] := by
        simpa [currentBase, counterTapes] using decodeEmpty
      have currentPower : currentBase (.inr .powerCounter) = [] := by
        simpa [currentBase, counterTapes] using powerEmpty
      have currentRepeat : currentBase (.inr .repetitionCounter) = [] := by
        simpa [currentBase, counterTapes] using repeatEmpty
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := edge_exec fixed K x e currentBase
        (guardState (some true)) (edgeFields x es) currentWord currentDecode
        currentPower currentRepeat
      have bodyRun' : Exec (GraphPackingProgram.edgeBody fixed K)
          ⟨guardState (some true), counterTapes (.inr .edgeCounter)
            (tapes (Numerator fixed) denominator base (inputs fixed K x start)
              (preparedOther fixed K x)) es.length⟩ bodySteps
          ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
            (tapes (Numerator fixed) denominator middleBase (inputs fixed K x (start + 1))
              (preparedOther fixed K x)) es.length⟩ := by
        simpa only [currentBase, middleBase, headIndex, resultBase_counter,
          ← layout_counter] using bodyRun
      have middleWord : middleBase (.inr .endpoints) = edgeFields x es := by
        simp [middleBase]
      have middleDecode : middleBase (.inr .decodeScratch) = [] := by
        simpa [middleBase] using decodeEmpty
      have middlePower : middleBase (.inr .powerCounter) = [] := by
        simpa [middleBase] using powerEmpty
      have middleRepeat : middleBase (.inr .repetitionCounter) = [] := by
        simpa [middleBase] using repeatEmpty
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih middleBase (start + 1)
        (.arithmetic (BinaryAddMachine.clean ())) tailIndices middleWord
        middleDecode middlePower middleRepeat
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · simp only [List.length_cons, Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (inputs fixed K x start)
                  (preparedOther fixed K x)) (es.length + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyAfterGuard : Exec (GraphPackingProgram.edgeBody fixed K)
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (inputs fixed K x start)
                  (preparedOther fixed K x)) (es.length + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
              (tapes (Numerator fixed) denominator middleBase (inputs fixed K x (start + 1))
                (preparedOther fixed K x)) es.length⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun'
        have combined := Exec.loop_true more bodyAfterGuard tailRun
        simpa only [PackingCountedProgram.loop, middleBase, resultBase_append,
          edgeWords, List.flatMap_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 es.length]
          using combined

def loopTimePolynomial : Polynomial Nat :=
  Polynomial.X * (edgeTimePolynomial fixed K + 1) + 1

theorem loop_exec (x : GraphReductionInput) (base : Tape fixed K → List Bool)
    (state : State)
    (sourceWord : base (.inr .endpoints) = GraphFieldMachine.fieldBits .endpoints x)
    (decodeEmpty : base (.inr .decodeScratch) = [])
    (powerEmpty : base (.inr .powerCounter) = [])
    (repeatEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ (loopTimePolynomial fixed K).eval (graphBits x).length,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (GraphPackingProgram.edgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (inputs fixed K x 0)
            (preparedOther fixed K x)) x.graph.edges.length⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (resultBase fixed K base [false]
              (PackingDescriptorExpression.rawRecords
                (PackingInventoryDescriptors.jobStream (inventory fixed K x))))
            (inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)) 0⟩ := by
  obtain ⟨steps, bound, run⟩ := loop_exec_list fixed K x
    (List.finRange x.graph.edges.length) base 0 state
    (by simpa only [List.length_finRange] using contiguous_finRange x.graph.edges.length)
    (by simpa only [edgeFields_finRange] using sourceWord) decodeEmpty powerEmpty repeatEmpty
  refine ⟨steps, ?_, ?_⟩
  · have hm := graph_edgeCount_le_bits x
    have upper := Nat.mul_le_mul_right
      ((edgeTimePolynomial fixed K).eval (graphBits x).length + 1) hm
    simp only [List.length_finRange] at bound
    simp only [loopTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one]
    omega
  · simpa only [List.length_finRange, Nat.zero_add, edgeWords_finRange] using run

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingPoolRuntime

open BinPackingGames.Foundations.Complexity
open GraphPackingRegisters GraphPackingGlobalPhases PackingInventoryDescriptors
open PackingItemExpression (denominator)

def tallyPolynomial (N : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 40 * (N + 1) ^ 3

@[simp] theorem tallyPolynomial_eval (N : Polynomial Nat) (s : Nat) :
    (tallyPolynomial N).eval s = 40 * (N.eval s + 1) ^ 3 := by
  simp only [tallyPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one]

theorem tally_le (n s : Nat) (N : Polynomial Nat) (hn : n ≤ N.eval s) :
    BinaryToTallyMachine.runtimeBound n ≤ (tallyPolynomial N).eval s := by
  have hsize : n.size ≤ N.eval s := (nat_size_le_self n).trans hn
  rw [tallyPolynomial_eval]
  unfold BinaryToTallyMachine.runtimeBound
  calc
    40 * (n + 1) * (n.size + 1) ^ 2 ≤
        40 * (N.eval s + 1) * (N.eval s + 1) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hn 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 2)
    _ = 40 * (N.eval s + 1) ^ 3 := by ring

def poolPolynomial (fixed : InventoryData) (descriptor : ItemDescriptor fixed)
    (N W : Polynomial Nat) : Polynomial Nat :=
  tallyPolynomial N + N *
    ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).comp W +
      Polynomial.C 2) + Polynomial.C 3

@[simp] theorem poolPolynomial_eval (fixed : InventoryData) (descriptor : ItemDescriptor fixed)
    (N W : Polynomial Nat) (s : Nat) :
    (poolPolynomial fixed descriptor N W).eval s =
      (tallyPolynomial N).eval s + N.eval s *
        ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).eval
          (W.eval s) + 2) + 3 := by
  simp only [poolPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_C]

theorem poolBudget_le (fixed : InventoryData) (K : Nat)
    (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (other : Other fixed K → Nat) (width : Nat) (N W : Polynomial Nat) (s : Nat)
    (hcount : other (GraphPackingProgram.otherSetup fixed K stock) ≤ N.eval s)
    (hwidth : width ≤ W.eval s) :
    GraphPackingPoolExec.poolBudget fixed K stock descriptor other width ≤
      (poolPolynomial fixed descriptor N W).eval s := by
  have ht := tally_le (other (GraphPackingProgram.otherSetup fixed K stock)) s N hcount
  have hb := MachineComposition.natPolynomial_eval_mono
    (PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]) hwidth
  have hm := Nat.mul_le_mul hcount (Nat.add_le_add_right hb 2)
  rw [poolPolynomial_eval]
  dsimp only [GraphPackingPoolExec.poolBudget]
  exact Nat.add_le_add_right (Nat.add_le_add ht hm) 3

def poolListPolynomial (fixed : InventoryData) (pools : List (Pool fixed))
    (N W : Polynomial Nat) : Polynomial Nat :=
  (pools.map (fun pool => poolPolynomial fixed pool.2 N W)).sum

@[simp] theorem poolListPolynomial_eval (fixed : InventoryData) (pools : List (Pool fixed))
    (N W : Polynomial Nat) (s : Nat) :
    (poolListPolynomial fixed pools N W).eval s =
      (pools.map (fun pool => (poolPolynomial fixed pool.2 N W).eval s)).sum := by
  simp only [poolListPolynomial, Polynomial.eval_listSum, List.map_map, Function.comp_def]

theorem poolListBudget_le (fixed : InventoryData) (K : Nat) (pools : List (Pool fixed))
    (other : Other fixed K → Nat) (width : Nat) (N W : Polynomial Nat) (s : Nat)
    (hcounts : ∀ pool ∈ pools,
      other (GraphPackingProgram.otherSetup fixed K pool.1) ≤ N.eval s)
    (hwidth : width ≤ W.eval s) :
    poolListBudget fixed K pools other width ≤
      (poolListPolynomial fixed pools N W).eval s := by
  revert hcounts
  induction pools with
  | nil =>
      intro _
      simp [poolListBudget, poolListPolynomial]
  | cons pool pools ih =>
      intro hcounts
      have headBound := poolBudget_le fixed K pool.1 pool.2 other width N W s
        (hcounts pool (by simp)) hwidth
      have tailBound := ih (fun p hp => hcounts p (by simp [hp]))
      simpa only [poolListBudget, poolListPolynomial, List.map_cons, List.sum_cons,
        Polynomial.eval_add] using Nat.add_le_add headBound tailBound

end BinPackingGap.GraphPackingPoolRuntime

namespace BinPackingGap.GraphPackingGlobalSemantics

open GraphPackingRegisters GraphPackingPreparation
open PackingDescriptorExpression PackingInventoryDescriptors GraphPackingStockStreams
open GraphPackingPoolExec GraphPackingGlobalPhases
open PackingItemExpression (Variable denominator)

variable (fixed : InventoryData) (K : Nat)

def inventory (x : GraphReductionInput) : InventoryData :=
  instantiate fixed x.graph (GraphPackingPreparation.repetitions fixed K x) x.k

def globalOutput {G : GraphInput} : GlobalSpecies G → PackingSetupExpression.Output
  | .up true => .upOne
  | .up false => .upZero
  | .um true => .umOne
  | .um false => .umZero
  | .edge _ _ => .edgeStock

def flagOutput : FlagSpecies → PackingSetupExpression.Output
  | .tree => .treeFlags
  | .main | .edge => .jobFlags

theorem prepared_output (x : GraphReductionInput) (o : PackingSetupExpression.Output) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K o) =
      PackingSetupExpression.inventoryOutput (inventory fixed K x) o := by
  change PackingSetupExpression.outputValues (parameters fixed K)
    x.graph.n x.graph.edges.length x.k o = _
  exact congrFun (PackingSetupExpression.outputValues_eq_inventory (parameters fixed K)
    (inventory fixed K x) rfl rfl rfl rfl) o

theorem prepared_globalStock (x : GraphReductionInput) (species : GlobalSpecies x.graph) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K (globalOutput species)) =
      (inventory fixed K x).globalStock species := by
  rw [prepared_output]
  cases species with
  | up one => cases one <;> rfl
  | um one => cases one <;> rfl
  | edge edge permit => rfl

theorem prepared_flagStock (x : GraphReductionInput) (species : FlagSpecies) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K (flagOutput species)) =
      (inventory fixed K x).flagStock species := by
  rw [prepared_output]
  cases species <;> rfl

theorem prepared_radix (x : GraphReductionInput) :
    GraphPackingGlobalLoop.radix fixed K (preparedOther fixed K x) =
      (inventory fixed K x).R + 1 := rfl

theorem prepared_globalCount (x : GraphReductionInput) :
    globalCount fixed K (preparedOther fixed K x) = x.graph.edges.length := rfl

theorem unitInput_values (x : GraphReductionInput) (label : Option x.graph.Vertex)
    (edge rep : Nat) :
    unitInput (values (inventory fixed K x) label edge rep) =
      values (inventory fixed K x) none 0 0 := by
  funext vinput
  cases vinput <;> simp [unitInput, values, NaturalPackingNumerator.labelPower]

theorem edgeInput_values (x : GraphReductionInput) (label : Option x.graph.Vertex)
    (oldEdge rep edge : Nat) :
    GraphPackingGlobalLoop.edgeInput fixed K
      (values (inventory fixed K x) label oldEdge rep) (preparedOther fixed K x) edge =
      values (inventory fixed K x) label edge rep := by
  funext vinput
  cases vinput <;>
    simp [GraphPackingGlobalLoop.edgeInput, prepared_radix, values]

theorem flagInput_values (x : GraphReductionInput) (edge : Nat) :
    flagInput (values (inventory fixed K x) none edge 0) =
      values (inventory fixed K x) none 0 0 := by
  funext vinput
  cases vinput <;> simp [flagInput, values]

theorem poolWord_global (x : GraphReductionInput) (species : GlobalSpecies x.graph) :
    poolWord fixed K (globalOutput species) (globalDescriptor (inventory fixed K x) species)
      (values (inventory fixed K x) none (globalEdgeIndex (inventory fixed K x) species) 0)
      (preparedOther fixed K x) =
      rawRecords (globalPoolStream (inventory fixed K x) species) := by
  unfold poolWord
  rw [prepared_globalStock]
  have hnum : numerator (inventory fixed K x) = numerator fixed := by
    funext descriptor
    exact numerator_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k descriptor
  have records := globalPool_chunk_records (inventory fixed K x) species
  rw [hnum] at records
  simpa only [Numerator, inventory, instantiate] using records

theorem poolWord_flag (x : GraphReductionInput) (species : FlagSpecies) :
    poolWord fixed K (flagOutput species) (flagDescriptor (inventory fixed K x) species)
      (values (inventory fixed K x) none 0 0) (preparedOther fixed K x) =
      rawRecords (flagPoolStream (inventory fixed K x) species) := by
  unfold poolWord
  rw [prepared_flagStock]
  have hnum : numerator (inventory fixed K x) = numerator fixed := by
    funext descriptor
    exact numerator_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k descriptor
  have records := flagPool_chunk_records (inventory fixed K x) species
  rw [hnum] at records
  simpa only [Numerator, inventory, instantiate] using records

theorem unitPools_word (x : GraphReductionInput) :
    poolListWord fixed K (unitPools fixed) (values (inventory fixed K x) none 0 0)
      (preparedOther fixed K x) =
      rawRecords (globalPoolStream (inventory fixed K x) (.up true) ++
        globalPoolStream (inventory fixed K x) (.up false) ++
        globalPoolStream (inventory fixed K x) (.um true) ++
        globalPoolStream (inventory fixed K x) (.um false)) := by
  have upOne := poolWord_global fixed K x (.up true)
  have upZero := poolWord_global fixed K x (.up false)
  have umOne := poolWord_global fixed K x (.um true)
  have umZero := poolWord_global fixed K x (.um false)
  dsimp only [globalOutput, globalDescriptor, globalEdgeIndex] at upOne upZero umOne umZero
  have words := congrArg₂ (fun a b : List Bool => a ++ b) upOne
    (congrArg₂ (fun a b : List Bool => a ++ b) upZero
      (congrArg₂ (fun a b : List Bool => a ++ b) umOne umZero))
  simpa only [poolListWord, unitPools, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    rawRecords, List.flatMap_append, List.append_assoc, inventory, instantiate] using words

theorem edgeWord_values (x : GraphReductionInput) (edge : x.graph.Edge) :
    GraphPackingGlobalLoop.edgeWord fixed K
      (values (inventory fixed K x) none edge.val 0) (preparedOther fixed K x) =
      rawRecords (globalPoolStream (inventory fixed K x) (.edge edge true) ++
        globalPoolStream (inventory fixed K x) (.edge edge false)) := by
  have yes := poolWord_global fixed K x (.edge edge true)
  have no := poolWord_global fixed K x (.edge edge false)
  dsimp only [globalOutput, globalDescriptor, globalEdgeIndex] at yes no
  simpa only [GraphPackingGlobalLoop.edgeWord, rawRecords, List.flatMap_append,
    inventory, instantiate] using
    congrArg₂ (fun a b : List Bool => a ++ b) yes no

theorem flagPools_word (x : GraphReductionInput) :
    poolListWord fixed K (flagPools fixed) (values (inventory fixed K x) none 0 0)
      (preparedOther fixed K x) = rawRecords (flagStream (inventory fixed K x)) := by
  have tree := poolWord_flag fixed K x .tree
  have main := poolWord_flag fixed K x .main
  have edge := poolWord_flag fixed K x .edge
  dsimp only [flagOutput, flagDescriptor] at tree main edge
  have words := congrArg₂ (fun a b : List Bool => a ++ b) tree
    (congrArg₂ (fun a b : List Bool => a ++ b) main edge)
  simpa only [poolListWord, flagPools, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    flagStream, rawRecords, List.flatMap_append, List.append_assoc, inventory, instantiate] using words

theorem globalsWord_eq (x : GraphReductionInput) :
    globalsWord fixed K (values (inventory fixed K x) none x.graph.edges.length 0)
      (preparedOther fixed K x) = rawRecords (globalStream (inventory fixed K x)) := by
  have unitValues := unitInput_values fixed K x none x.graph.edges.length 0
  have unitWords := unitPools_word fixed K x
  have edgeValues := edgeInput_values fixed K x none 0 0
  have edgeWords := edgeWord_values fixed K x
  dsimp only [inventory, instantiate] at unitValues unitWords edgeValues edgeWords ⊢
  unfold globalsWord
  rw [unitValues, unitWords, prepared_globalCount fixed K x,
    GraphPackingGlobalLoop.stream_eq_finRange]
  simp_rw [Nat.zero_add, edgeValues, edgeWords]
  simp only [globalStream, rawRecords, List.flatMap_append, List.flatMap_assoc,
    List.append_assoc]

theorem globalsInput_eq (x : GraphReductionInput) :
    globalsInput fixed K (values (inventory fixed K x) none x.graph.edges.length 0)
      (preparedOther fixed K x) =
      values (inventory fixed K x) none x.graph.edges.length 0 := by
  have unitValues := unitInput_values fixed K x none x.graph.edges.length 0
  have edgeValues := edgeInput_values fixed K x none 0 0 x.graph.edges.length
  dsimp only [inventory, instantiate] at unitValues edgeValues ⊢
  unfold globalsInput
  rw [unitValues, prepared_globalCount fixed K x]
  exact edgeValues

theorem flagInput_eq (x : GraphReductionInput) :
    flagInput (values (inventory fixed K x) none x.graph.edges.length 0) =
      values (inventory fixed K x) none 0 0 :=
  flagInput_values fixed K x x.graph.edges.length

theorem flagsWord_eq (x : GraphReductionInput) :
    poolListWord fixed K (flagPools fixed)
      (flagInput (values (inventory fixed K x) none x.graph.edges.length 0))
      (preparedOther fixed K x) = rawRecords (flagStream (inventory fixed K x)) := by
  rw [flagInput_eq, flagPools_word]

end BinPackingGap.GraphPackingGlobalSemantics

namespace BinPackingGap.GraphPackingGlobalRuntime

open GraphPackingRegisters GraphPackingPreparation GraphPackingGlobalPhases
open GraphPackingPoolRuntime
open PackingItemExpression (denominator)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def adjustedWidthPolynomial : Polynomial Nat :=
  GraphPackingStockBounds.widthPolynomial fixed K + 1

def edgeWidthPolynomial : Polynomial Nat :=
  adjustedWidthPolynomial fixed K +
    Polynomial.X * GraphPackingStockBounds.widthPolynomial fixed K + 1

def resetPolynomial : Polynomial Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .labelPower 0).comp (adjustedWidthPolynomial fixed K) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .repetitionOne 0).comp (adjustedWidthPolynomial fixed K) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).comp (adjustedWidthPolynomial fixed K)

def edgeBodyPolynomial : Polynomial Nat :=
  poolPolynomial fixed (.w, .globalEdge true)
    (GraphPackingStockBounds.stockPolynomial fixed K) (edgeWidthPolynomial fixed K) +
  poolPolynomial fixed (.w, .globalEdge false)
    (GraphPackingStockBounds.stockPolynomial fixed K) (edgeWidthPolynomial fixed K) +
  Polynomial.C 64 * (GraphPackingStockBounds.widthPolynomial fixed K +
    edgeWidthPolynomial fixed K + 1) ^ 2 + 1

def flagsPolynomial : Polynomial Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).comp (adjustedWidthPolynomial fixed K) +
  poolListPolynomial fixed (flagPools fixed)
    (GraphPackingStockBounds.stockPolynomial fixed K) (adjustedWidthPolynomial fixed K) + 1

def globalsPolynomial : Polynomial Nat :=
  resetPolynomial fixed K +
  poolListPolynomial fixed (unitPools fixed)
    (GraphPackingStockBounds.stockPolynomial fixed K) (adjustedWidthPolynomial fixed K) +
  tallyPolynomial Polynomial.X + Polynomial.X * (edgeBodyPolynomial fixed K + 1) + 3

private theorem width_le (x : GraphReductionInput) :
    GraphPackingWidths.width fixed K x ≤
      (GraphPackingStockBounds.widthPolynomial fixed K).eval (graphBits x).length := by
  rw [GraphPackingStockBounds.widthPolynomial_eval]
  exact GraphPackingStockBounds.preparationWidth_le fixed K x

private theorem adjustedWidth_le (x : GraphReductionInput) :
    GraphPackingWidths.width fixed K x + 1 ≤
      (adjustedWidthPolynomial fixed K).eval (graphBits x).length := by
  simpa only [adjustedWidthPolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right (width_le fixed K x) 1

private theorem radixWidth_le (x : GraphReductionInput) :
    (GraphPackingGlobalLoop.radix fixed K (preparedOther fixed K x)).size ≤
      (GraphPackingStockBounds.widthPolynomial fixed K).eval (graphBits x).length :=
  GraphPackingStockBounds.preparedOther_size_le_polynomial fixed K x
    (GraphPackingProgram.otherSetup fixed K .base)

private theorem stockCount_le (x : GraphReductionInput) (stock : PackingSetupExpression.Output)
    (selected : stock ∈ [.upOne, .upZero, .umOne, .umZero, .edgeStock, .treeFlags, .jobFlags]) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K stock) ≤
      (GraphPackingStockBounds.stockPolynomial fixed K).eval (graphBits x).length := by
  rw [GraphPackingGlobalSemantics.prepared_output]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.up true)
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.up false)
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.um true)
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.um false)
  · have hm : 0 < x.graph.edges.length := by
      cases h : x.graph.edges with
      | nil => exact False.elim (x.nonempty h)
      | cons e rest => simp
    exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.edge ⟨0, hm⟩ true)
  · exact GraphPackingStockBounds.flagStock_le_polynomial fixed K x .tree
  · exact GraphPackingStockBounds.flagStock_le_polynomial fixed K x .main

private theorem unitCounts_le (x : GraphReductionInput) :
    ∀ pool ∈ unitPools fixed,
      preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K pool.1) ≤
        (GraphPackingStockBounds.stockPolynomial fixed K).eval (graphBits x).length := by
  intro pool hp
  simp only [unitPools, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    exact stockCount_le fixed K x _ (by simp)

private theorem flagCounts_le (x : GraphReductionInput) :
    ∀ pool ∈ flagPools fixed,
      preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K pool.1) ≤
        (GraphPackingStockBounds.stockPolynomial fixed K).eval (graphBits x).length := by
  intro pool hp
  simp only [flagPools, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    exact stockCount_le fixed K x _ (by simp)

theorem aggregateWidth_le (x : GraphReductionInput) :
    GraphPackingGlobalLoop.aggregateWidth fixed K (preparedOther fixed K x)
      (GraphPackingWidths.width fixed K x + 1) 0
      (globalCount fixed K (preparedOther fixed K x)) ≤
      (edgeWidthPolynomial fixed K).eval (graphBits x).length := by
  have hw := adjustedWidth_le fixed K x
  have hm := Nat.mul_le_mul (graph_edgeCount_le_bits x) (radixWidth_le fixed K x)
  rw [GraphPackingGlobalLoop.aggregateWidth, GraphPackingGlobalSemantics.prepared_globalCount]
  simp only [Nat.zero_add, edgeWidthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

private theorem resetBudget_le (x : GraphReductionInput) :
    resetBudget fixed K (GraphPackingWidths.width fixed K x) ≤
      (resetPolynomial fixed K).eval (graphBits x).length := by
  have h₁ := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 0) (adjustedWidth_le fixed K x)
  have h₂ := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0) (adjustedWidth_le fixed K x)
  have h₃ := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1) (adjustedWidth_le fixed K x)
  simpa only [resetBudget, resetPolynomial, Polynomial.eval_add, Polynomial.eval_comp] using
    Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃

private theorem bodyBudget_le (x : GraphReductionInput) (width : Nat)
    (hw : width ≤ (edgeWidthPolynomial fixed K).eval (graphBits x).length) :
    GraphPackingGlobalLoop.bodyBudget fixed K (preparedOther fixed K x) width ≤
      (edgeBodyPolynomial fixed K).eval (graphBits x).length := by
  have hc := stockCount_le fixed K x .edgeStock (by simp)
  have h₁ := poolBudget_le fixed K .edgeStock (.w, .globalEdge true)
    (preparedOther fixed K x) width (GraphPackingStockBounds.stockPolynomial fixed K)
    (edgeWidthPolynomial fixed K) (graphBits x).length hc hw
  have h₂ := poolBudget_le fixed K .edgeStock (.w, .globalEdge false)
    (preparedOther fixed K x) width (GraphPackingStockBounds.stockPolynomial fixed K)
    (edgeWidthPolynomial fixed K) (graphBits x).length hc hw
  have hsquare := Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add (radixWidth_le fixed K x) hw) 1) 2
  have hmul := Nat.mul_le_mul_left 64 hsquare
  simp only [GraphPackingGlobalLoop.bodyBudget, edgeBodyPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one]
  omega

theorem flagsBudget_le (x : GraphReductionInput) :
    flagsBudget fixed K (preparedOther fixed K x) (GraphPackingWidths.width fixed K x) ≤
      (flagsPolynomial fixed K).eval (graphBits x).length := by
  have hr := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1) (adjustedWidth_le fixed K x)
  have hp := poolListBudget_le fixed K (flagPools fixed) (preparedOther fixed K x)
    (GraphPackingWidths.width fixed K x + 1) (GraphPackingStockBounds.stockPolynomial fixed K)
    (adjustedWidthPolynomial fixed K) (graphBits x).length
    (flagCounts_le fixed K x) (adjustedWidth_le fixed K x)
  simpa only [flagsBudget, flagsPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_one] using Nat.add_le_add_right (Nat.add_le_add hr hp) 1

theorem globalsBudget_le (x : GraphReductionInput) :
    globalsBudget fixed K (preparedOther fixed K x) (GraphPackingWidths.width fixed K x) ≤
      (globalsPolynomial fixed K).eval (graphBits x).length := by
  have hr := resetBudget_le fixed K x
  have hp := poolListBudget_le fixed K (unitPools fixed) (preparedOther fixed K x)
    (GraphPackingWidths.width fixed K x + 1) (GraphPackingStockBounds.stockPolynomial fixed K)
    (adjustedWidthPolynomial fixed K) (graphBits x).length
    (unitCounts_le fixed K x) (adjustedWidth_le fixed K x)
  have hc : globalCount fixed K (preparedOther fixed K x) ≤ (graphBits x).length := by
    rw [GraphPackingGlobalSemantics.prepared_globalCount]
    exact graph_edgeCount_le_bits x
  have ht := tally_le (globalCount fixed K (preparedOther fixed K x))
    (graphBits x).length Polynomial.X (by simpa only [Polynomial.eval_X] using hc)
  have hb := bodyBudget_le fixed K x _ (aggregateWidth_le fixed K x)
  have hl := Nat.mul_le_mul hc (Nat.add_le_add_right hb 1)
  simp only [globalsBudget, globalsPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  omega

end BinPackingGap.GraphPackingGlobalRuntime

namespace BinPackingGap.GraphPackingGlobalExecution

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters GraphPackingPreparation
open PackingItemExpression (denominator)
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

theorem globals_exec (x : GraphReductionInput)
    (base : GraphPackingRegisters.Tape fixed K → List Bool) (state : State)
    (poolEmpty : base (.inr .poolCounter) = [])
    (edgeEmpty : base (.inr .edgeCounter) = []) :
    ∃ steps ≤ (GraphPackingGlobalRuntime.globalsPolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.globals fixed K)
        ⟨state, tapes (Numerator fixed) denominator base
          (GraphPackingJobs.inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (PackingDescriptorExpression.rawRecords
                (PackingInventoryDescriptors.globalStream (GraphPackingJobs.inventory fixed K x))))
            (GraphPackingJobs.inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)⟩ := by
  have counterZero : preparedOther fixed K x (.inr .counter) = 0 := rfl
  have oneZero : preparedOther fixed K x (.inr .one) = 0 := rfl
  have temporaryZero : preparedOther fixed K x (.inr .temporary) = 0 := rfl
  obtain ⟨steps, bound, run⟩ := GraphPackingGlobalPhases.globals_exec fixed K base
    (PackingDescriptorExpression.values (GraphPackingGlobalSemantics.inventory fixed K x)
      none x.graph.edges.length 0) (preparedOther fixed K x) state
    (GraphPackingWidths.width fixed K x) counterZero oneZero temporaryZero poolEmpty edgeEmpty
    (GraphPackingStockBounds.values_width fixed K x x.graph.edges.length le_rfl)
    (GraphPackingWidths.preparedOther_width fixed K x)
  refine ⟨steps, bound.trans (GraphPackingGlobalRuntime.globalsBudget_le fixed K x), ?_⟩
  rw [GraphPackingGlobalSemantics.globalsWord_eq,
    GraphPackingGlobalSemantics.globalsInput_eq] at run
  simpa only [GraphPackingJobs.inputs_eq_values, GraphPackingJobs.inventory,
    GraphPackingGlobalSemantics.inventory, PackingDescriptorExpression.instantiate] using run

theorem flags_exec (x : GraphReductionInput)
    (base : GraphPackingRegisters.Tape fixed K → List Bool) (state : State)
    (poolEmpty : base (.inr .poolCounter) = []) :
    ∃ steps ≤ (GraphPackingGlobalRuntime.flagsPolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.flags fixed K)
        ⟨state, tapes (Numerator fixed) denominator base
          (GraphPackingJobs.inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (PackingDescriptorExpression.rawRecords
                (PackingInventoryDescriptors.flagStream (GraphPackingJobs.inventory fixed K x))))
            (GraphPackingJobs.inputs fixed K x 0) (preparedOther fixed K x)⟩ := by
  have counterZero : preparedOther fixed K x (.inr .counter) = 0 := rfl
  have oneZero : preparedOther fixed K x (.inr .one) = 0 := rfl
  have temporaryZero : preparedOther fixed K x (.inr .temporary) = 0 := rfl
  obtain ⟨steps, bound, run⟩ := GraphPackingGlobalPhases.flags_exec fixed K base
    (PackingDescriptorExpression.values (GraphPackingGlobalSemantics.inventory fixed K x)
      none x.graph.edges.length 0) (preparedOther fixed K x) state
    (GraphPackingWidths.width fixed K x) counterZero oneZero temporaryZero poolEmpty
    (GraphPackingStockBounds.values_width fixed K x x.graph.edges.length le_rfl)
    (GraphPackingWidths.preparedOther_width fixed K x)
  refine ⟨steps, bound.trans (GraphPackingGlobalRuntime.flagsBudget_le fixed K x), ?_⟩
  rw [GraphPackingGlobalSemantics.flagsWord_eq, GraphPackingGlobalSemantics.flagInput_eq] at run
  simpa only [GraphPackingJobs.inputs_eq_values, GraphPackingJobs.inventory,
    GraphPackingGlobalSemantics.inventory, PackingDescriptorExpression.instantiate] using run

end BinPackingGap.GraphPackingGlobalExecution

end

end OAI
