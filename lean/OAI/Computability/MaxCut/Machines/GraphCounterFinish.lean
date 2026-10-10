import Mathlib
import OAI.Computability.MaxCut.Machines.MachineLazyTableRuntime

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterFinish

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
  simpa only [List.length_append, List.length_reverse, initialState] using! h

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

end MaxCutGames.Foundations.Complexity.GraphCounterFinish

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterPrefix

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
    have hi := @List.map_id (machine.Γ machine.k₀) (GraphTables.tableBits table)
    have ho := @List.map_id (machine.Γ machine.k₁) (output table)
    rw [hi, ho]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] using outputsInTime table

end MaxCutGames.Foundations.Complexity.GraphCounterPrefix

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

namespace MaxCutGames.Foundations.Complexity.PCPIterationMachine

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

/-- The exponent is a fixed growth constant, independent of the input. -/
theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

/-- This recurrence concerns semantic cardinality, not unary encoding length. -/
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

/-- A polynomial in initial semantic size; two extra steps include the final
zero guard and actual halt. The encoding polynomial is applied once. -/
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

/-- A concrete guard and halt are added to the supplied body statements.
The body may return to `Sum.inl false`; it starts at `Sum.inr entry`. -/
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

/-- Finite packaging of the concrete control program. Callers supply a fixed
finite body; no input-dependent collection of labels or states is introduced. -/
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

/-- Full loop execution including the final transition that consumes the
counter delimiter and halts, retaining the unread suffix. The only supplied
execution hypotheses concern individual body calls in this same program. -/
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

/-- Actual body costs are bounded through a semantic-size sequence and a
separate encoding polynomial. Index `rounds n - (r+1)` is the forward round
corresponding to the unary guard's remaining-count index `r`. -/
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

/-- Timed execution of the concrete guard/body/halt program. This compositional
interface is not a certificate for an unprovided graph-transformation body. -/
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

end MaxCutGames.Foundations.Complexity.PCPIterationMachine

end OAI
