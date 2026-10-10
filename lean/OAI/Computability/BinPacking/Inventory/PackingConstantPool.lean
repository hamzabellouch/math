import OAI.Computability.BinPacking.Machines.PackingJobLoop

namespace OAI

noncomputable section

namespace BinPackingGap.PackingConstantPool

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler PairExpressionCompiler
open PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ K : Type} [DecidableEq α] [DecidableEq K]

def repeatRecords (word : List Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => word ++ repeatRecords word n

def code (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output counter : K) (descriptors : List δ) : Code (K := K) (S := State) :=
  PackingCountedProgram.loop counter
    (PackingArithmeticProgram.code
      (PackingChunkMachine.code numerator denominator slot output descriptors))

theorem output_counter_comm (output counter : K) (different : counter ≠ output)
    (base : K → List Bool) (n : Nat) (word : List Bool) :
    outputTapes output (counterTapes counter base n) word =
      counterTapes counter (outputTapes output base word) n := by
  funext k
  by_cases ho : k = output
  · subst k
    simp [outputTapes, counterTapes, Ne.symm different]
  · by_cases hc : k = counter
    · subst k
      simp [outputTapes, counterTapes, different]
    · simp [outputTapes, counterTapes, ho, hc, Ne.symm different]

theorem shape_after_counter {R : Type} (slot : (R ⊕ Fin 6) ↪ K)
    (counter : K) (outside : ∀ i, slot i ≠ counter) (base : K → List Bool)
    (values : R → Nat) (shape : registerTapes slot base values = base) (n : Nat) :
    registerTapes slot (counterTapes counter base n) values = counterTapes counter base n := by
  classical
  unfold counterTapes
  rw [RegisterFrameEmission.external_update slot base values counter outside, shape]

theorem exec (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output counter : K) (different : counter ≠ output)
    (outsideOutput : ∀ d i, slot d i ≠ output)
    (outsideCounter : ∀ d i, slot d i ≠ counter)
    (descriptors : List δ) (base : K → List Bool) (values : δ → α → Nat)
    (state : State) (width n : Nat)
    (shape : ∀ d ∈ descriptors,
      registerTapes (slot d) base (initial (numerator d) denominator (values d)) = base)
    (hwidth : ∀ d ∈ descriptors, ∀ a, (values d a).size ≤ width) :
    ∃ steps ≤ n * ((PackingChunkMachine.timePolynomial numerator denominator descriptors).eval width + 2) + 1,
      Exec (code numerator denominator slot output counter descriptors)
        ⟨state, counterTapes counter base n⟩ steps
        ⟨guardState none, outputTapes output (counterTapes counter base 0)
          (repeatRecords (PackingChunkMachine.records numerator denominator values descriptors) n)⟩ := by
  induction n generalizing base state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have h : PackingCountedProgram.more ((PackingCountedProgram.guard counter).eval
          ⟨state, counterTapes counter base 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [code, PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        repeatRecords, PackingChunkMachine.outputTapes_nil] using
        (Exec.loop_false (a := PackingArithmeticProgram.code
          (PackingChunkMachine.code numerator denominator slot output descriptors)) h)
  | succ n ih =>
      let word := PackingChunkMachine.records numerator denominator values descriptors
      let middle := outputTapes output base word
      have counterShape : ∀ d ∈ descriptors,
          registerTapes (slot d) (counterTapes counter base n)
            (initial (numerator d) denominator (values d)) = counterTapes counter base n := by
        intro d hd
        exact shape_after_counter (slot d) counter (outsideCounter d) base _ (shape d hd) n
      have chunkRun := PackingChunkMachine.exec numerator denominator slot output outsideOutput
        descriptors (counterTapes counter base n) values () width counterShape hwidth
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := PackingArithmeticProgram.exec_in_time
        (PackingChunkMachine.code numerator denominator slot output descriptors)
        (counterTapes counter base n) (outputTapes output (counterTapes counter base n) word)
        ((PackingChunkMachine.timePolynomial numerator denominator descriptors).eval width)
        (guardState (some true)) chunkRun
      have middleShape : ∀ d ∈ descriptors,
          registerTapes (slot d) middle
            (initial (numerator d) denominator (values d)) = middle := by
        intro d hd
        exact PackingChunkMachine.shape_after_output (slot d) output (outsideOutput d)
          base _ (shape d hd) word
      obtain ⟨tailSteps, tailBound, tailRun⟩ :=
        ih middle (.arithmetic (BinaryAddMachine.clean ())) middleShape
      have guardTrue : PackingCountedProgram.more ((PackingCountedProgram.guard counter).eval
          ⟨state, counterTapes counter base (n + 1)⟩).state = true := by
        rw [PackingCountedProgram.guard_succ]
        rfl
      have bodyRun' : Exec
          (PackingArithmeticProgram.code
            (PackingChunkMachine.code numerator denominator slot output descriptors))
          ((PackingCountedProgram.guard counter).eval
            ⟨state, counterTapes counter base (n + 1)⟩) bodySteps
          ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes counter middle n⟩ := by
        rw [PackingCountedProgram.guard_succ]
        simpa only [output_counter_comm output counter different, middle] using bodyRun
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
      · have combined := Exec.loop_true guardTrue bodyRun' tailRun
        have finalFrame : outputTapes output (counterTapes counter middle 0)
            (repeatRecords word n) =
            outputTapes output (counterTapes counter base 0) (repeatRecords word (n + 1)) := by
          change outputTapes output (counterTapes counter (outputTapes output base word) 0)
            (repeatRecords word n) = _
          rw [← output_counter_comm output counter different,
            PackingChunkMachine.outputTapes_append]
          rfl
        simpa only [code, PackingCountedProgram.loop, finalFrame, word] using combined

theorem exec_from_tapes (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output counter : K) (different : counter ≠ output)
    (outsideOutput : ∀ d i, slot d i ≠ output)
    (outsideCounter : ∀ d i, slot d i ≠ counter)
    (descriptors : List δ) (base : K → List Bool) (values : δ → α → Nat)
    (state : State) (width n : Nat)
    (counterWord : base counter = List.replicate n true)
    (shape : ∀ d ∈ descriptors,
      registerTapes (slot d) base (initial (numerator d) denominator (values d)) = base)
    (hwidth : ∀ d ∈ descriptors, ∀ a, (values d a).size ≤ width) :
    ∃ steps ≤ n * ((PackingChunkMachine.timePolynomial numerator denominator descriptors).eval width + 2) + 1,
      Exec (code numerator denominator slot output counter descriptors)
        ⟨state, base⟩ steps
        ⟨guardState none, outputTapes output (counterTapes counter base 0)
          (repeatRecords (PackingChunkMachine.records numerator denominator values descriptors) n)⟩ := by
  have initialCounter : counterTapes counter base n = base := by
    unfold counterTapes
    rw [← counterWord, Function.update_eq_self]
  simpa only [initialCounter] using exec numerator denominator slot output counter different
    outsideOutput outsideCounter descriptors base values state width n shape hwidth

theorem final_frame (output counter : K) (base : K → List Bool) (word : List Bool)
    (k : K) (notOutput : k ≠ output) (notCounter : k ≠ counter) :
    outputTapes output (counterTapes counter base 0) word k = base k := by
  simp [outputTapes, counterTapes, notOutput, notCounter]

end BinPackingGap.PackingConstantPool

end

end OAI
