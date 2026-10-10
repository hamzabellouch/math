import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineLazyTableRuntime

namespace OAI

namespace DFVSGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

private theorem trace_trans_inline_GraphCounterFinish {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem start_eq (counter rest original : List Bool) :
    clockConfiguration (extraTapes rest original) none
      (haltList MachineLogCounter.machine counter) =
      ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩ := by
  rw [MachineLogCounter.haltList_eq]
  unfold clockConfiguration
  congr 1
  funext tape
  cases tape with
  | inl i => fin_cases i <;> simp [clockTapes, frame, MachineLogCounter.configuration,
      MachineLogCounter.rawTapes]
  | inr k => cases k <;> rfl

theorem finish_eq (word : List Bool) :
    (⟨none, initialState, frame [] [] [] [] word⟩ : TM2.Cfg Alphabet Label State) =
      haltList machine word := by
  unfold haltList
  congr 1
  funext tape
  cases tape with
  | inl i => simp [machine, frame]
  | inr k =>
    cases k <;> simp [machine, frame]
    rfl

theorem drainTrace (rest original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[rest.length + 1]
      (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) =
      some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩ := by
  have h := (MachineDrain.drainInTime (Sum.inr ExtraTape.input) (Sum.inr ExtraLabel.clearInput)
    (some (.inr .clockCopy)) program rfl (frame rest original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rest.length + 1]
    (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) = _ at h
  have update : Function.update (frame rest original counter [] []) (.inr .input) [] =
      frame [] original counter [] [] := by
    funext tape
    cases tape with
    | inl i => simp [frame]
    | inr k => cases k <;> simp [frame]
  simpa only [update, initialState] using h

theorem clockCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[counter.length + 1]
      (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) =
      some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inl (2 : Fin 3))
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .clockCopy)
    (some (.inr .archiveCopy)) program rfl (frame [] original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[counter.length + 1]
    (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inl (2 : Fin 3))
      (Sum.inr ExtraTape.scratch) (frame [] original counter [] []) []
        ((frame [] original counter [] [] (.inl 2)).reverse.map id ++
          frame [] original counter [] [] (.inr .scratch)) =
      frame [] original [] counter.reverse [] := by
    funext tape
    cases tape with
    | inl i => fin_cases i <;> simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem archiveCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + 1]
      (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) =
      some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.archive)
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .archiveCopy)
    (some (.inr .finalReverse)) program rfl (frame [] original [] counter.reverse [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[original.length + 1]
    (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.archive)
      (Sum.inr ExtraTape.scratch) (frame [] original [] counter.reverse []) []
        ((frame [] original [] counter.reverse [] (.inr .archive)).reverse.map id ++
          frame [] original [] counter.reverse [] (.inr .scratch)) =
      frame [] [] [] (original.reverse ++ counter.reverse) [] := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem reverseTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + counter.length + 1]
      (some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩) =
      some (haltList machine (counter ++ original)) := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.scratch)
    (Sum.inr ExtraTape.output) (by decide) id false (.inr .finalReverse) none program rfl
    (frame [] [] [] (original.reverse ++ counter.reverse) []) MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
    (original.reverse ++ counter.reverse).length + 1]
    (some ⟨some (.inr .finalReverse), initialState,
      frame [] [] [] (original.reverse ++ counter.reverse) []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.scratch)
      (Sum.inr ExtraTape.output) (frame [] [] [] (original.reverse ++ counter.reverse) []) []
        ((frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .scratch)).reverse.map id ++
          frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .output)) =
      frame [] [] [] [] (counter ++ original) := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  rw [update] at h
  rw [← finish_eq]
  simp only [List.length_append, List.length_reverse, initialState] at h
  exact h

theorem finishTrace (counter rest original : List Bool) :
    (MachineComposition.advance (TM2.step program))^[
        rest.length + 2 * counter.length + 2 * original.length + 4]
      (some (clockConfiguration (extraTapes rest original) none
        (haltList MachineLogCounter.machine counter))) =
      some (haltList machine (counter ++ original)) := by
  rw [start_eq]
  have total := trace_trans_inline_GraphCounterFinish _
    (trace_trans_inline_GraphCounterFinish _ (trace_trans_inline_GraphCounterFinish _ (drainTrace rest original counter)
      (clockCopyTrace original counter)) (archiveCopyTrace original counter))
    (reverseTrace original counter)
  simpa only [show rest.length + 1 + (counter.length + 1) + (original.length + 1) +
      (original.length + counter.length + 1) =
      rest.length + 2 * counter.length + 2 * original.length + 4 by omega] using total

def finishInTime (counter rest original : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration (extraTapes rest original) none (haltList MachineLogCounter.machine counter))
      (some (haltList machine (counter ++ original)))
      (rest.length + 2 * counter.length + 2 * original.length + 4) where
  steps := rest.length + 2 * counter.length + 2 * original.length + 4
  evals_in_steps := finishTrace counter rest original
  steps_le_m := le_rfl

end DFVSGames.Foundations.Complexity.GraphCounterFinish

namespace DFVSGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawOutput (n m : Nat) (rest : List Bool) : List Bool :=
  encodeWord ((n + m).log2 + 1) ++ (encodeWords [n, m] ++ rest)

def rawInTime (n m : Nat) (rest : List Bool) :
    TM2OutputsInTime machine (encodeWords [n, m] ++ rest) (some (rawOutput n m rest))
      (20 * (encodeWords [n, m] ++ rest).length + 30) := by
  let original := encodeWords [n, m] ++ rest
  let start := startInTime n m rest
  let clock := clockInTime (extraTapes rest original) none (n + m)
  let finish := finishInTime (encodeWord ((n + m).log2 + 1)) rest original
  have start' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine original)
      (some (clockConfiguration (extraTapes rest original) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * (original.length + 1) + 1 + (n + 1) + (m + 1)) := start
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start' clock
  let total := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  refine { toEvalsTo := total.toEvalsTo, steps_le_m := ?_ }
  have bound := total.steps_le_m
  have hlog := Nat.log2_le_self (n + m)
  have hlength : original.length = n + m + 2 + rest.length := by
    simp only [original, List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  simp only [encodeWord_length] at bound
  change total.steps ≤ 20 * original.length + 30
  omega

def count (table : GraphTables.Table) : Nat := (table.vertices + table.darts).log2 + 1

def output (table : GraphTables.Table) : List Bool :=
  encodeWord (count table) ++ GraphTables.tableBits table

def rowsBits (table : GraphTables.Table) : List Bool :=
  encodeWords ((GraphTables.rowList table).flatMap GraphTables.rowWords)

theorem tableBits_decomposition (table : GraphTables.Table) :
    GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table :=
  encodeWords_append _ _

def outputsInTime (table : GraphTables.Table) :
    TM2OutputsInTime machine (GraphTables.tableBits table) (some (output table))
      (20 * (GraphTables.tableBits table).length + 30) := by
  have run := rawInTime table.vertices table.darts (rowsBits table)
  simpa only [rawOutput, output, count, tableBits_decomposition] using run

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits id output where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun table := by
    change TM2OutputsInTime machine ((GraphTables.tableBits table).map id)
      (some ((output table).map id))
      ((20 * Polynomial.X + 30 : Polynomial Nat).eval (GraphTables.tableBits table).length)
    have input_eq := @List.map_id (machine.Γ machine.k₀) (GraphTables.tableBits table)
    have output_eq := @List.map_id (machine.Γ machine.k₁) (output table)
    rw [input_eq, output_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    exact outputsInTime table

end DFVSGames.Foundations.Complexity.GraphCounterPrefix

namespace DFVSGames.Foundations.Complexity.PCPIterationMachine

open Turing
open MachineCountedLoop

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

noncomputable def timePolynomial (growth : Nat)
    (encodingSize bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) *
    ((bodyTime.comp encodingSize).comp (sizePolynomial growth) + 1) + 2

@[simp] theorem timePolynomial_eval (growth n : Nat)
    (encodingSize bodyTime : Polynomial Nat) :
    (timePolynomial growth encodingSize bodyTime).eval n =
      (n + 1) * (bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)) + 1) + 2 := by
  simp [timePolynomial]

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool
abbrev Labels (Λ : Type) := Bool ⊕ Λ

def program (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) :
    Labels Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)
  | .inl false => MachineUnaryCounter.guard counter (.inr entry) (.inl true)
  | .inl true => .pop counter (fun state _ => (state.1, none)) .halt
  | .inr label => body label

omit [DecidableEq K] in
@[simp] theorem program_guard (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) :
    program counter entry body (.inl false) =
      MachineUnaryCounter.guard counter (.inr entry) (.inl true) := rfl

def machine [Fintype K] [Fintype Λ] [Fintype σ]
    (counter output : K) (entry : Λ) (initial : σ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) : FinTM2 where
  K := K
  k₀ := counter
  k₁ := output
  Γ := Alphabet
  Λ := Labels Λ
  main := .inl false
  σ := State σ
  initialState := (initial, none)
  m := program counter entry body

def haltedConfiguration (counter : K) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) (Labels Λ) (State σ) :=
  ⟨none, (ambient 0, none), Function.update (base 0) counter suffix⟩

theorem haltStep (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ))
    (suffix : List Bool) (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.step (program counter entry body)
      (exitConfiguration counter (.inl true) suffix ambient base) =
      some (haltedConfiguration counter suffix ambient base) := by
  change some (TM2.stepAux (.pop counter (fun state _ => (state.1, none)) .halt)
    (ambient 0, none) (MachineUnaryCounter.counterTapes counter (base 0) 0 suffix)) = _
  simp [TM2.stepAux, MachineUnaryCounter.counterTapes, encodeWord, haltedConfiguration]

theorem iterationTrace (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter (.inl false) (.inr entry)
      (program counter entry body) suffix ambient register base cost (rounds n)) :
    (MachineComposition.advance (TM2.step (program counter entry body)))^[
        totalSteps cost (rounds n) + 1]
      (some (guardConfiguration counter (.inl false) suffix ambient register base (rounds n))) =
      some (haltedConfiguration counter suffix ambient base) := by
  rw [Function.iterate_succ_apply']
  rw [loopTrace counter (.inl false) (.inr entry) (.inl true)
    (program counter entry body) (program_guard counter entry body) suffix
    ambient register base cost (rounds n) bodyTraces]
  exact haltStep counter entry body suffix ambient base

theorem bodyCosts_bound (growth n : Nat) (growthPositive : 0 < growth)
    (sizes encodedSizes cost : Nat → Nat) (encodingSize bodyTime : Polynomial Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (encodingBound : ∀ r, r < rounds n →
      encodedSizes r ≤ encodingSize.eval (sizes (rounds n - (r + 1))))
    (bodyCost : ∀ r, r < rounds n → cost r ≤ bodyTime.eval (encodedSizes r)) :
    ∀ r, r < rounds n →
      cost r ≤ bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)) := by
  intro r hr
  have hs := semanticSize_bound sizes growth n growthPositive initialBound growthBound
    (rounds n - (r + 1)) (Nat.sub_le _ _)
  exact (bodyCost r hr).trans
    (MachineComposition.natPolynomial_eval_mono bodyTime
      ((encodingBound r hr).trans
        (MachineComposition.natPolynomial_eval_mono encodingSize hs)))

def iterationInTime (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (bodyTraces : BodyTraces counter (.inl false) (.inr entry)
      (program counter entry body) suffix ambient register base cost (rounds n))
    (sizes encodedSizes : Nat → Nat) (encodingSize bodyTime : Polynomial Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (encodingBound : ∀ r, r < rounds n →
      encodedSizes r ≤ encodingSize.eval (sizes (rounds n - (r + 1))))
    (bodyCost : ∀ r, r < rounds n → cost r ≤ bodyTime.eval (encodedSizes r)) :
    StateTransition.EvalsToInTime (TM2.step (program counter entry body))
      (guardConfiguration counter (.inl false) suffix ambient register base (rounds n))
      (some (haltedConfiguration counter suffix ambient base))
      ((timePolynomial growth encodingSize bodyTime).eval n) where
  steps := totalSteps cost (rounds n) + 1
  evals_in_steps := iterationTrace counter entry body suffix ambient register base cost n bodyTraces
  steps_le_m := by
    rw [timePolynomial_eval]
    have h := totalSteps_le cost (rounds n)
      (bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)))
      (bodyCosts_bound growth n growthPositive sizes encodedSizes cost encodingSize bodyTime
        initialBound growthBound encodingBound bodyCost)
    have hm := Nat.mul_le_mul_right
      (bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)) + 1) (rounds_le n)
    omega

end DFVSGames.Foundations.Complexity.PCPIterationMachine

namespace DFVSGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

noncomputable def lengthPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp (PCPIterationMachine.sizePolynomial sizeFactor)

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

noncomputable def runtimePolynomial (bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (bodyTime.comp lengthPolynomial + 2 * lengthPolynomial + 4) +
    2 * lengthPolynomial + 4

theorem runtimePolynomial_eval (bodyTime : Polynomial Nat) (N : Nat) :
    (runtimePolynomial bodyTime).eval N =
      (N + 1) * (bodyTime.eval (lengthPolynomial.eval N) + 2 * lengthPolynomial.eval N + 4) +
        2 * lengthPolynomial.eval N + 4 := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]

end DFVSGames.Foundations.Complexity.GraphIterationBounds

namespace DFVSGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

def clauseSigns {n : Nat} (c : Clause n) : Signs :=
  ((c)[0].positive, (c)[1].positive, (c)[2].positive)

def clauseNames {n : Nat} (c : Clause n) : Names :=
  ((c)[0].variableIndex.val, (c)[1].variableIndex.val, (c)[2].variableIndex.val)

def nameWord (names : Names) : Slot → Nat
  | .first => names.1
  | .second => names.2.1
  | .third => names.2.2

def decodedLabel (a : GraphTables.Label) : InitialGraph.Label :=
  AlphabetRetraction.decode64 (labelOrder.symm a)

def incidencePredicate (signs : Signs) (slot : Slot)
    (clauseLabel variableLabel : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid variableLabel &&
    (((literalValue signs.1 clauseLabel.1 ||
      literalValue signs.2.1 clauseLabel.2.1) ||
      literalValue signs.2.2 clauseLabel.2.2) &&
      decide (answerAt (InitialGraph.toClauseAnswer clauseLabel) slot = variableLabel.1))

def relationPredicate (signs : Signs) (slot : Slot) :
    Bool → GraphTables.Label → GraphTables.Label → Bool
  | false, a, b => incidencePredicate signs slot (decodedLabel a) (decodedLabel b)
  | true, a, b => incidencePredicate signs slot (decodedLabel b) (decodedLabel a)

def relationWordsFor (signs : Signs) (slot : Slot) (orientation : Bool) : List Nat :=
  relationWords (relationOf (relationPredicate signs slot orientation))

@[simp] theorem relationWordsFor_length (signs : Signs) (slot : Slot) (orientation : Bool) :
    (relationWordsFor signs slot orientation).length = 4096 := by
  exact relationWords_length _

def incidenceWords (n i : Nat) (names : Names) (signs : Signs)
    (slot : Slot) (orientation : Bool) : List Nat :=
  [if orientation then nameWord names slot else n + i,
    6 * i + 2 * (slotOrder slot).val + (if orientation then 0 else 1)] ++
      relationWordsFor signs slot orientation

def clauseWords (n i : Nat) (names : Names) (signs : Signs) : List Nat :=
  incidenceWords n i names signs .first false ++
  incidenceWords n i names signs .first true ++
  incidenceWords n i names signs .second false ++
  incidenceWords n i names signs .second true ++
  incidenceWords n i names signs .third false ++
  incidenceWords n i names signs .third true

def dummyWords (n m : Nat) : List Nat :=
  [n + m, 6 * m] ++ List.replicate 4096 1

end DFVSGames.Foundations.PCP.RawInitialRows

namespace DFVSGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def orderedList {α : Type*} {n : Nat} (e : α ≃ Fin n) : List α :=
  List.ofFn e.symm

theorem orderedList_cast {α : Type*} {m n : Nat} (e : α ≃ Fin m) (h : m = n) :
    orderedList (e.trans (finCongr h)) = orderedList e := by
  subst n
  rfl

theorem orderedList_prod {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.prodCongr f).trans finProdFinEquiv) =
      (orderedList e).flatMap (fun a => (orderedList f).map (fun b => (a, b))) := by
  change List.ofFn (fun q : Fin (m * n) =>
    (e.symm (finProdFinEquiv.symm q).1, f.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [orderedList, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val * n + j.val, by
      calc
        i.val * n + j.val < (i.val + 1) * n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
        _ ≤ m * n := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (m * n)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem orderedList_sum {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.sumCongr f).trans finSumFinEquiv) =
      (orderedList e).map Sum.inl ++ (orderedList f).map Sum.inr := by
  change List.ofFn (fun q : Fin (m + n) =>
    (e.sumCongr f).symm (finSumFinEquiv.symm q)) = _
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin m =>
    (e.sumCongr f).symm (finSumFinEquiv.symm (i.castAdd n)))) ++
    (List.ofFn (fun i : Fin n =>
      (e.sumCongr f).symm (finSumFinEquiv.symm (i.natAdd m)))) = _
  simp [orderedList, List.map_ofFn]
  rfl

def clauseDarts (F : Formula) (i : Fin F.clauses.length) : List (InitialGraph.Dart F) :=
  [.inl ((i, .first), false), .inl ((i, .first), true),
   .inl ((i, .second), false), .inl ((i, .second), true),
   .inl ((i, .third), false), .inl ((i, .third), true)]

theorem orderedList_dartOrder (F : Formula) :
    orderedList (dartOrder F) =
      (List.finRange F.clauses.length).flatMap (clauseDarts F) ++ [.inr ()] := by
  rw [dartOrder, orderedList_cast, orderedList_sum, orderedList_prod]
  rw [eventOrder, orderedList_prod]
  have hs : orderedList slotOrder = [.first, .second, .third] := rfl
  have hb : orderedList finTwoEquiv.symm = [false, true] := rfl
  have hu : orderedList unitOrder = [()] := rfl
  rw [hs, hb, hu]
  simp [orderedList, List.finRange, List.flatMap_assoc, List.map_flatMap,
    ]
  rfl

def rowFor (F : Formula) (d : InitialGraph.Dart F) :
    DartRow (F.«variables» + F.clauses.length + 1) (6 * F.clauses.length + 1) where
  tail := vertexOrder F (InitialGraph.tail F d)
  reverseIndex := dartOrder F (InitialGraph.reverse F d)
  relation := relationOf (fun a b => InitialGraph.predicate F d (decodedLabel a) (decodedLabel b))

theorem rowList_table (F : Formula) :
    rowList (table F) = (orderedList (dartOrder F)).map (rowFor F) := by
  simp only [rowList, table, ofEnumeratedGraph, ofGraph, graphRows, Vector.toList_ofFn,
    orderedList, List.map_ofFn]
  rfl

theorem rowWords_incidence (F : Formula) (i : Fin F.clauses.length)
    (slot : Slot) (orientation : Bool) :
    rowWords (rowFor F (.inl ((i, slot), orientation))) =
      incidenceWords F.«variables» i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) slot orientation := by
  have ht : (rowFor F (.inl ((i, slot), orientation))).tail.val =
      if orientation then nameWord (clauseNames (clauseAt F i)) slot else F.«variables» + i.val := by
    cases orientation <;> cases slot <;> rfl
  have hr : (rowFor F (.inl ((i, slot), orientation))).reverseIndex.val =
      6 * i.val + 2 * (slotOrder slot).val + (if orientation then 0 else 1) := by
    cases orientation <;> cases slot <;>
      simp [rowFor, InitialGraph.reverse, dartOrder, eventOrder, slotOrder, unitOrder,
        finProdFinEquiv, finSumFinEquiv, finTwoEquiv, Nat.mul_add,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]
  have hp : (rowFor F (.inl ((i, slot), orientation))).relation =
      relationOf (relationPredicate (clauseSigns (clauseAt F i)) slot orientation) := by
    cases orientation <;> rfl
  unfold rowWords incidenceWords relationWordsFor
  rw [ht, hr, hp]

theorem rowWords_dummy (F : Formula) :
    rowWords (rowFor F (.inr ())) = dummyWords F.«variables» F.clauses.length := by
  have ht : (rowFor F (.inr ())).tail.val = F.«variables» + F.clauses.length := rfl
  have hr : (rowFor F (.inr ())).reverseIndex.val = 6 * F.clauses.length := by
    simp [rowFor, InitialGraph.reverse, dartOrder, unitOrder, finSumFinEquiv]
  have hp : (rowFor F (.inr ())).relation = relationOf (fun _ _ => true) := rfl
  have hw : relationWords (relationOf (fun _ _ => true)) = List.replicate 4096 1 := by
    unfold relationWords
    rw [relationOf, Vector.toList_ofFn, List.map_ofFn]
    exact List.ofFn_const 4096 1
  unfold rowWords dummyWords
  rw [ht, hr, hp, hw]

theorem clauseDarts_rowWords (F : Formula) (i : Fin F.clauses.length) :
    (clauseDarts F i).flatMap (fun d => rowWords (rowFor F d)) =
      clauseWords F.«variables» i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) := by
  simp [clauseDarts, rowWords_incidence, clauseWords, List.append_assoc]

theorem tableWords_eq (F : Formula) :
    tableWords (table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
      (List.finRange F.clauses.length).flatMap (fun i =>
        clauseWords F.«variables» i.val (clauseNames (clauseAt F i))
          (clauseSigns (clauseAt F i))) ++ dummyWords F.«variables» F.clauses.length := by
  rw [tableWords, rowList_table, orderedList_dartOrder]
  simp [List.flatMap_map, List.flatMap_append, List.flatMap_assoc, clauseDarts_rowWords,
    rowWords_dummy]

end DFVSGames.Foundations.PCP.RawInitialRows

namespace DFVSGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq, Fintype

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

def copySource : CopyPhase → Tape
  | .tailVariables _ | .dummyVariables => .«variables»
  | .variableName slot => .field (nameField slot)
  | _ => .index

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

def finalTape (slot : Fin 3) : Tape :=
  if slot.val = 0 then .«variables» else if slot.val = 1 then .counter else .index

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  MachineDrain.drain tape again (some next)

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .«variables» else .counter

def relationOutput (slot : Fin 3) (orientation : Bool) (state : State) : List Bool :=
  (encodeWords (RawInitialRows.relationWordsFor state.1
    (RawInitialTables.slotOrder.symm slot) orientation)).reverse

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (if slot.val = 0 then some (.headerStart 1) else some .scanN)
  | .scanN => MachineInitialHeaders.prefixScan .«variables» .scratch .reversed 1 .scanN .restoreN
  | .restoreN => Reduction.MachineTransfer.loopAt .scratch .«variables» id false .restoreN (some .scanM1)
  | .scanM1 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 1 .scanM1 .restoreM1
  | .restoreM1 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM1 (some .closeFirst)
  | .closeFirst => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .scanM6)
  | .scanM6 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 6 .scanM6 .restoreM6
  | .restoreM6 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM6 (some .closeSecond)
  | .closeSecond => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .initializeIndex)
  | .initializeIndex => .push .index (fun _ => false) (.goto fun _ => .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.scan .dummyVariables)
  | .fieldStart slot => SourceMachine.fieldStart (.field slot) (.fieldLoop slot)
  | .fieldLoop slot => SourceMachine.fieldLoop .input (.field slot) (.fieldLoop slot)
      (if h : slot.val + 1 < 6 then some (.fieldStart ⟨slot.val + 1, h⟩)
        else some .loadSigns)
  | .loadSigns =>
      .peek (.field 1) (fun state head => ((head.getD false, state.1.2), state.2))
        (.peek (.field 3) (fun state head => ((state.1.1, head.getD false, state.1.2.2), state.2))
          (.peek (.field 5) (fun state head => ((state.1.1, state.1.2.1, head.getD false), state.2))
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan (.tailVariables 0)))))
  | .scan phase => MachineInitialHeaders.prefixScan (copySource phase) .scratch .reversed
      (copyScale phase) (.scan phase) (.restore phase)
  | .restore phase => Reduction.MachineTransfer.loopAt .scratch (copySource phase) id false
      (.restore phase) (some (copyNext phase))
  | .closeTail slot orientation => .push .reversed (fun _ => false)
      (.goto fun _ => .scan (.reverseIndex slot orientation))
  | .closeReverse slot orientation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWord (2 * slot.val + if orientation then 0 else 1))
        (.goto fun _ => .relation slot orientation)
  | .relation slot orientation => MachineFiniteTable.emit .reversed
      (relationOutput slot orientation)
      stateKeys (.goto fun _ => relationNext slot orientation)
  | .cleanupField slot => drain (.field slot) (.cleanupField slot)
      (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩ else .incrementIndex)
  | .incrementIndex => .push .index (fun _ => true) (.goto fun _ => .guard)
  | .closeDummyTail => .push .reversed (fun _ => false) (.goto fun _ => .scan .dummyReverse)
  | .closeDummyReverse => .push .reversed (fun _ => false) (.goto fun _ => .dummyRelation)
  | .dummyRelation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWords (GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true))))
        (.goto fun _ => .cleanupFinal 0)
  | .cleanupFinal slot => drain (finalTape slot) (.cleanupFinal slot)
      (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩ else .reset)
  | .reset => .load (fun _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end DFVSGames.Foundations.PCP.RawInitialMachineModel

end OAI
