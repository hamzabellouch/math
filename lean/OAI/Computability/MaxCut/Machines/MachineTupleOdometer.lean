import Mathlib
import OAI.Computability.MaxCut.Machines.MachineUnaryMultiply

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

abbrev digitTapes (current remaining : K) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) : K → List Bool :=
  MachineUnaryAddAt.unaryTapes current remaining base d r currentSuffix remainingSuffix

def increment (current remaining : K) (doneLabel resetLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek remaining (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop remaining (fun state _ => (state.1, none))
        (.push current (fun _ => true) (.goto fun _ => doneLabel)))
      (.load (fun state => (state.1, none)) (.goto fun _ => resetLabel)))

/-- Reset conserves the digit's unary budget, then enters the next coordinate. -/
def reset (current remaining : K) (resetLabel carryLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineUnaryAddAt.loop current remaining resetLabel (some carryLabel)

omit [DecidableEq K] in
theorem incrementPushBound (current remaining : K) (doneLabel resetLabel : Λ) :
    Runtime.statementPushBound (increment (σ := σ) current remaining doneLabel resetLabel) =
      1 := rfl

omit [DecidableEq K] in
theorem resetPushBound (current remaining : K) (resetLabel carryLabel : Λ) :
    Runtime.statementPushBound (reset (σ := σ) current remaining resetLabel carryLabel) =
      1 := rfl

private theorem update_current_inline_MachineTupleOdometer (current remaining : K) (distinct : current ≠ remaining)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt current remaining base input output) current replacement =
      tapesAt current remaining base replacement output := by
  funext k
  by_cases hc : k = current
  · subst k; simp [tapesAt, distinct]
  · by_cases hr : k = remaining
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hc, hr]

private theorem update_remaining_inline_MachineTupleOdometer (current remaining : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt current remaining base input output) remaining replacement =
      tapesAt current remaining base input replacement := by
  simp [tapesAt]

theorem stepAux_increment_succ (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix) =
      ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord, List.replicate_succ, update_current_inline_MachineTupleOdometer, update_remaining_inline_MachineTupleOdometer]

theorem stepAux_increment_zero (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d 0 currentSuffix remainingSuffix) =
      ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord]

/-- A non-carrying digit increment is one actual ambient-program transition. -/
theorem incrementStep_succ (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix⟩ =
      some ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_succ current remaining distinct]

theorem incrementStep_zero (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ =
      some ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_zero current remaining distinct]

theorem resetTrace (current remaining : K) (distinct : current ≠ remaining)
    (resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 1]
      (some ⟨some resetLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 (d + r) currentSuffix remainingSuffix⟩ :=
  MachineUnaryAddAt.addTrace current remaining distinct resetLabel (some carryLabel)
    program atReset base d r currentSuffix remainingSuffix ambient register

/-- Exhaustion costs one check plus the actual `d + 1`-transition reset. -/
theorem carryTrace (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 2]
      (some ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 d currentSuffix remainingSuffix⟩ := by
  rw [show d + 2 = (d + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[d + 1]
    (TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) = _
  rw [incrementStep_zero current remaining distinct checkLabel doneLabel resetLabel
    program atCheck]
  simpa only [Nat.add_zero] using resetTrace current remaining distinct resetLabel carryLabel
    program atReset base d 0 currentSuffix remainingSuffix ambient none

/-- The exact step count for one digit, including its possible reset. -/
def digitSteps (d r : ℕ) : ℕ := if r = 0 then d + 2 else 1

/-- The bounded digit operation follows actual transitions on both branches.
It restores an exhausted digit to zero before returning the carry. -/
theorem digitTrace (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[digitSteps d r]
      (some ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩) =
      some ⟨some (if r = 0 then carryLabel else doneLabel), (ambient, none),
        digitTapes current remaining base (if r = 0 then 0 else d + 1)
          (if r = 0 then d else r - 1) currentSuffix remainingSuffix⟩ := by
  cases r with
  | zero =>
    simpa only [digitSteps, ↓reduceIte] using carryTrace current remaining distinct
      checkLabel doneLabel resetLabel carryLabel program atCheck atReset base d
      currentSuffix remainingSuffix ambient register
  | succ r =>
    simpa only [digitSteps, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      Function.iterate_one, MachineComposition.advance_some] using
        incrementStep_succ current remaining distinct checkLabel doneLabel resetLabel
          program atCheck base d r currentSuffix remainingSuffix ambient register

omit [DecidableEq K] in
theorem digitSteps_le (n d r : ℕ) (hn : 0 < n) (budget : d + r = n - 1) :
    digitSteps d r ≤ n + 1 := by
  unfold digitSteps
  split <;> omega

omit [DecidableEq K] in
theorem digitBudget (n d r : ℕ) (_hn : 0 < n) (budget : d + r = n - 1) :
    (if r = 0 then 0 else d + 1) + (if r = 0 then d else r - 1) = n - 1 := by
  by_cases hr : r = 0 <;> simp only [hr, ↓reduceIte] <;> omega

/-- Every unrelated stack is preserved, including any separate stored radix
or input bound. Both digit-stack suffixes are preserved by the trace itself. -/
theorem digitFrame (current remaining other : K)
    (notCurrent : other ≠ current) (notRemaining : other ≠ remaining)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool) :
    digitTapes current remaining base (if r = 0 then 0 else d + 1)
      (if r = 0 then d else r - 1) currentSuffix remainingSuffix other =
      digitTapes current remaining base d r currentSuffix remainingSuffix other := by
  simp only [digitTapes, MachineUnaryAddAt.unaryTapes_other current remaining other
    notCurrent notRemaining]

/-- A composable actual-time witness for any well-formed positive-radix digit. -/
def digitInTime (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (n d r : ℕ) (hn : 0 < n) (budget : d + r = n - 1)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩
      (some ⟨some (if r = 0 then carryLabel else doneLabel), (ambient, none),
        digitTapes current remaining base (if r = 0 then 0 else d + 1)
          (if r = 0 then d else r - 1) currentSuffix remainingSuffix⟩) (n + 1) where
  steps := digitSteps d r
  evals_in_steps := digitTrace current remaining distinct checkLabel doneLabel resetLabel
    carryLabel program atCheck atReset base d r currentSuffix remainingSuffix ambient register
  steps_le_m := digitSteps_le n d r hn budget

section AscendingCycle

open scoped BigOperators

def bodyConfiguration (current remaining : K) (bodyLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (remainder + 1), none),
    digitTapes current remaining (base (remainder + 1)) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def checkConfiguration (current remaining : K) (checkLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some checkLabel, (ambient remainder, register remainder),
    digitTapes current remaining (base remainder) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def cycleExit (current remaining : K) (exitLabel : Λ)
    (maximum : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none),
    digitTapes current remaining (base 0) 0 maximum currentSuffix remainingSuffix⟩

def VisitTraces (current remaining : K) (bodyLabel checkLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (maximum count : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) : Prop :=
  ∀ r, r ≤ count → (MachineComposition.advance (TM2.step program))^[cost r]
    (some (bodyConfiguration current remaining bodyLabel maximum r
      currentSuffix remainingSuffix ambient base)) =
    some (checkConfiguration current remaining checkLabel maximum r
      currentSuffix remainingSuffix ambient register base)

def cycleSteps (cost : ℕ → ℕ) (maximum count : ℕ) : ℕ :=
  (∑ r ∈ Finset.range (count + 1), cost r) + count + maximum + 2

private theorem cycleSteps_zero_inline_MachineTupleOdometer (cost : ℕ → ℕ) (maximum : ℕ) :
    cycleSteps cost maximum 0 = (maximum + 2) + cost 0 := by
  simp [cycleSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem cycleSteps_succ_inline_MachineTupleOdometer (cost : ℕ → ℕ) (maximum count : ℕ) :
    cycleSteps cost maximum (count + 1) =
      (cycleSteps cost maximum count + 1) + cost (count + 1) := by
  simp only [cycleSteps, Finset.sum_range_succ]
  omega

theorem cycleTrace (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (maximum count : ℕ) (hcount : count ≤ maximum)
    (currentSuffix remainingSuffix : List Bool) (ambient : ℕ → σ)
    (register : ℕ → Option Bool) (base : ℕ → K → List Bool) (cost : ℕ → ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program maximum count
      currentSuffix remainingSuffix ambient register base cost) :
    (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (some (bodyConfiguration current remaining bodyLabel maximum count
        currentSuffix remainingSuffix ambient base)) =
      some (cycleExit current remaining exitLabel maximum
        currentSuffix remainingSuffix ambient base) := by
  induction count with
  | zero =>
    rw [cycleSteps_zero_inline_MachineTupleOdometer, Function.iterate_add_apply, visits 0 (Nat.le_refl 0)]
    simpa only [checkConfiguration, cycleExit, Nat.sub_zero] using
      carryTrace current remaining distinct checkLabel bodyLabel resetLabel exitLabel
        program atCheck atReset (base 0) maximum currentSuffix remainingSuffix
        (ambient 0) (register 0)
  | succ count ih =>
    rw [cycleSteps_succ_inline_MachineTupleOdometer, Function.iterate_add_apply, visits (count + 1) (Nat.le_refl _),
      Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (TM2.step program ⟨some checkLabel, (ambient (count + 1), register (count + 1)),
        digitTapes current remaining (base (count + 1)) (maximum - (count + 1))
          (count + 1) currentSuffix remainingSuffix⟩) = _
    rw [incrementStep_succ current remaining distinct checkLabel bodyLabel resetLabel
      program atCheck]
    have hnext : maximum - (count + 1) + 1 = maximum - count := by omega
    rw [hnext]
    exact ih (by omega) (fun r hr => visits r (by omega))

/-- A full positive-radix cycle performs `n` body visits and exactly `2*n`
counter transitions. This bound comes from the composed actual execution. -/
def ascendingCycleInTime (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (n : ℕ) (hn : 0 < n) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) (B : ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program (n - 1) (n - 1)
      currentSuffix remainingSuffix ambient register base cost)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (bodyConfiguration current remaining bodyLabel (n - 1) (n - 1)
        currentSuffix remainingSuffix ambient base)
      (some (cycleExit current remaining exitLabel (n - 1)
        currentSuffix remainingSuffix ambient base)) (n * (B + 2)) where
  steps := cycleSteps cost (n - 1) (n - 1)
  evals_in_steps := cycleTrace current remaining distinct bodyLabel checkLabel resetLabel exitLabel
    program atCheck atReset (n - 1) (n - 1) (Nat.le_refl _) currentSuffix remainingSuffix
    ambient register base cost visits
  steps_le_m := by
    have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
      calc
        _ ≤ ∑ _r ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
        _ = _ := by simp
    have hn' : n - 1 + 1 = n := by omega
    simp only [cycleSteps, hn', Nat.mul_add] at *
    omega

end AscendingCycle

section Order

omit [DecidableEq K]

open scoped BigOperators

def tupleOrder (n q : ℕ) : List (Fin q → Fin n) :=
  List.ofFn (finFunctionFinEquiv (m := n) (n := q)).symm

theorem tupleOrder_length (n q : ℕ) : (tupleOrder n q).length = n ^ q := by
  simp [tupleOrder]

/-- Dimension zero visits the unique empty tuple once, even at radix zero. -/
theorem tupleOrder_dimension_zero (n : ℕ) :
    tupleOrder n 0 = [fun i => Fin.elim0 i] := by
  simp only [tupleOrder, pow_zero, List.ofFn_succ, List.ofFn_zero, List.cons.injEq,
    and_true]
  funext i
  exact Fin.elim0 i

/-- A positive-dimensional zero-radix loop has no tuples to visit. -/
theorem tupleOrder_radix_zero {q : ℕ} (hq : 0 < q) : tupleOrder 0 q = [] := by
  apply List.length_eq_zero_iff.mp
  rw [tupleOrder_length, Nat.zero_pow hq]

/-- Coordinate zero is the least significant digit. This is the same radix
rank used by `SourceOccurrences.Encoding.function`. -/
theorem tupleRank_cons {n q : ℕ} (d : Fin n) (tail : Fin q → Fin n) :
    (finFunctionFinEquiv (Fin.cons d tail)).val =
      d.val + n * (finFunctionFinEquiv tail).val := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
  congr 1
  rw [finFunctionFinEquiv_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem tupleRank_increment_lowest {n q : ℕ} (d d' : Fin n)
    (tail : Fin q → Fin n) (hsucc : d'.val = d.val + 1) :
    (finFunctionFinEquiv (Fin.cons d' tail)).val =
      (finFunctionFinEquiv (Fin.cons d tail)).val + 1 := by
  rw [tupleRank_cons, tupleRank_cons, hsucc]
  omega

/-- Resetting an exhausted low digit and incrementing the tail advances the
same explicit tuple rank by one. -/
theorem tupleRank_carry {n q : ℕ} (hn : 0 < n) (d : Fin n)
    (tail tail' : Fin q → Fin n) (hmax : d.val = n - 1)
    (htail : (finFunctionFinEquiv tail').val = (finFunctionFinEquiv tail).val + 1) :
    (finFunctionFinEquiv (Fin.cons (⟨0, hn⟩ : Fin n) tail')).val =
      (finFunctionFinEquiv (Fin.cons d tail)).val + 1 := by
  rw [tupleRank_cons, tupleRank_cons, htail, hmax]
  simp only [Nat.zero_add, Nat.mul_add, Nat.mul_one]
  omega

theorem tupleRank_snoc {n q : ℕ} (tail : Fin q → Fin n) (d : Fin n) :
    (finFunctionFinEquiv (Fin.snoc tail d)).val =
      (finFunctionFinEquiv tail).val + d.val * n ^ q := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

theorem tupleOrder_snoc (n q : ℕ) :
    tupleOrder n (q + 1) = (List.ofFn (fun d : Fin n => d)).flatMap
      (fun d => (tupleOrder n q).map (fun tail => Fin.snoc tail d)) := by
  change List.ofFn (fun rank : Fin (n ^ q * n) =>
    (finFunctionFinEquiv (m := n) (n := q + 1)).symm rank) = _
  rw [List.ofFn_mul']
  simp only [tupleOrder, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext d
  apply congrArg List.ofFn
  funext rank
  dsimp only [Function.comp_apply]
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  erw [Equiv.apply_symm_apply, tupleRank_snoc, Equiv.apply_symm_apply]
  simp [Nat.mul_comm, Nat.add_comm]

end Order

section Nested

open scoped BigOperators

/-- Explicit caller state and tape endpoints for one level of the nested
loop. Compatibility with its child schedules is checked by their types. -/
structure CycleSchedule (K σ : Type) where
  currentSuffix : List Bool
  remainingSuffix : List Bool
  ambient : ℕ → σ
  register : ℕ → Option Bool
  base : ℕ → K → List Bool

abbrev Configuration (K Λ σ : Type) :=
  TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool)

/-- A finite nesting schedule. Only leaves supply actual emitter traces.
Internal nodes supply concrete instruction placements and compatible endpoint
schedules; their complete execution is derived below. Level `q` operates
coordinate `q`, so coordinate zero is always the innermost loop. -/
inductive NestedCycle (n : ℕ) (current remaining : ℕ → K) (bodyLabel : Λ)
    (checkLabel resetLabel : ℕ → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    ℕ → Λ → Configuration K Λ σ → Configuration K Λ σ → Type where
  | leaf (exitLabel : Λ) (start finish : Configuration K Λ σ) (count : ℕ)
      (atBody : start.l = some bodyLabel) (atExit : finish.l = some exitLabel)
      (run : (MachineComposition.advance (TM2.step program))^[count] (some start) = some finish) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        0 exitLabel start finish
  | node (depth : ℕ) (exitLabel : Λ) (positive : 0 < n)
      (distinct : current depth ≠ remaining depth)
      (atCheck : program (checkLabel depth) =
        increment (current depth) (remaining depth) bodyLabel (resetLabel depth))
      (atReset : program (resetLabel depth) =
        reset (current depth) (remaining depth) (resetLabel depth) exitLabel)
      (s : CycleSchedule K σ)
      (children : ∀ r : Fin n,
        NestedCycle n current remaining bodyLabel checkLabel resetLabel program
          depth (checkLabel depth)
          (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.base)
          (checkConfiguration (current depth) (remaining depth) (checkLabel depth) (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.register s.base)) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        (depth + 1) exitLabel
        (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (current depth) (remaining depth) exitLabel (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)

omit [DecidableEq K] in
/-- Exact concrete-counter overhead for a complete positive-radix nesting. -/
def counterOverhead (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => n * (counterOverhead n q + 2)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def steps {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children =>
    cycleSteps (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) (n - 1) (n - 1)
termination_by depth

/-- Every supplied emitter leaf obeys its local time allowance. There is no
whole-loop runtime premise at any internal node. -/
def LeafBound (B : ℕ) {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : Prop :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count ≤ B
  | .node _ _ _ _ _ _ _ children => ∀ r, LeafBound B (children r)
termination_by depth

/-- Sum of the actual supplied emitter costs, with no counter work included. -/
def work {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children => ∑ r : Fin n, work (children r)
termination_by depth

def reverseDigit (d : Fin n) : Fin n := ⟨n - 1 - d.val, by omega⟩

theorem reverseDigit_current (d : Fin n) : n - 1 - (reverseDigit d).val = d.val := by
  dsimp only [reverseDigit]
  omega

def order {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : List (Fin depth → Fin n) :=
  match tree with
  | .leaf _ _ _ _ _ _ _ => [fun i => Fin.elim0 i]
  | .node _ _ _ _ _ _ _ children =>
    (List.ofFn (fun d : Fin n => d)).flatMap (fun d =>
      (order (children (reverseDigit d))).map (fun tail => Fin.snoc tail d))
termination_by depth

theorem order_eq_tupleOrder {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : tree.order = tupleOrder n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [order] using (tupleOrder_dimension_zero n).symm
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [order, ih, tupleOrder_snoc]

theorem order_length {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : tree.order.length = n ^ depth := by
  rw [order_eq_tupleOrder, tupleOrder_length]

theorem steps_eq_work_add_overhead {depth : ℕ} {exitLabel : Λ}
    {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : tree.steps = tree.work + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simp only [steps, work, counterOverhead, Nat.add_zero]
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    have hn : n - 1 + 1 = n := by omega
    have hsum : (∑ r ∈ Finset.range n,
        if hr : r < n then steps (children ⟨r, hr⟩) else 0) =
        (∑ r : Fin n, work (children r)) + n * counterOverhead n depth := by
      calc
        _ = ∑ r : Fin n, steps (children r) := by
          rw [← Fin.sum_univ_eq_sum_range]
          simp only [Fin.isLt, ↓reduceDIte]
        _ = ∑ r : Fin n, (work (children r) + counterOverhead n depth) := by
          apply Finset.sum_congr rfl
          intro r _
          exact ih r
        _ = _ := by simp [Finset.sum_add_distrib]
    simp only [steps, work, cycleSteps, hn, hsum, counterOverhead, Nat.mul_add]
    omega

/-- The whole nested-loop trace is derived from its actual leaf traces and
the concrete increment/reset code. -/
theorem trace {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) :
    (MachineComposition.advance (TM2.step program))^[tree.steps] (some start) = some finish := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run => simpa only [steps] using run
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [steps]
    apply cycleTrace (current depth) (remaining depth) distinct bodyLabel (checkLabel depth)
      (resetLabel depth) exitLabel program atCheck atReset (n - 1) (n - 1)
      (Nat.le_refl _) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
    intro r hr
    have hlt : r < n := by omega
    simpa only [dite_eq_left hlt] using ih ⟨r, hlt⟩

theorem steps_le {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ n ^ depth * B + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [steps, LeafBound, counterOverhead, pow_zero, Nat.one_mul, Nat.add_zero] using bounded
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [LeafBound] at bounded
    have visits : VisitTraces (current depth) (remaining depth) bodyLabel (checkLabel depth)
        program (n - 1) (n - 1) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
        (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) := by
      intro r hr
      have hlt : r < n := by omega
      simpa only [dite_eq_left hlt] using (children ⟨r, hlt⟩).trace
    have bodyBound : ∀ r, r < n →
        (if hr : r < n then steps (children ⟨r, hr⟩) else 0) ≤
          n ^ depth * B + counterOverhead n depth := by
      intro r hr
      simpa only [dite_eq_left hr] using ih ⟨r, hr⟩ (bounded ⟨r, hr⟩)
    have h := (ascendingCycleInTime (current depth) (remaining depth) distinct bodyLabel
      (checkLabel depth) (resetLabel depth) exitLabel program atCheck atReset n positive
      s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
      (n ^ depth * B + counterOverhead n depth) visits bodyBound).steps_le_m
    change cycleSteps _ (n - 1) (n - 1) ≤ _ at h
    simpa only [steps, counterOverhead, pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc] using h

/-- An actual-time certificate for the complete fixed-dimensional schedule. -/
def inTime {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    StateTransition.EvalsToInTime (TM2.step program) start (some finish)
      (n ^ depth * B + counterOverhead n depth) where
  steps := tree.steps
  evals_in_steps := tree.trace
  steps_le_m := tree.steps_le B bounded

end NestedCycle

omit [DecidableEq K] in
theorem counterOverhead_le (n q : ℕ) (hn : 0 < n) :
    counterOverhead n q ≤ 2 * q * n ^ q := by
  induction q with
  | zero => simp [counterOverhead]
  | succ q ih =>
    have hp : 1 ≤ n ^ q := by apply Nat.one_le_pow; exact hn
    have h := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 2)
    have htwo : 2 ≤ 2 * n ^ q := Nat.mul_le_mul_left 2 hp
    have hinner : 2 * q * n ^ q + 2 ≤ 2 * (q + 1) * n ^ q := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    exact h.trans (by
      simpa only [counterOverhead, pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using Nat.mul_le_mul_left n hinner)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

theorem steps_le_power {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (hn : 0 < n) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ (B + 2 * depth) * n ^ depth := by
  have h := (tree.steps_le B bounded).trans
    (Nat.add_le_add_left (counterOverhead_le n depth hn) (n ^ depth * B))
  simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

end NestedCycle

end Nested

/-- The actual entry guard bypasses an empty positive-dimensional Cartesian
product. Dimension zero always enters its one empty-tuple emitter. -/
def entry (q : ℕ) (radix : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  if q = 0 then
    .load (fun state => (state.1, none)) (.goto fun _ => bodyLabel)
  else
    .peek radix (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => bodyLabel))
        (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

theorem entryStep_dimension_zero (radix : K) (startLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = entry 0 radix bodyLabel exitLabel)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some startLabel, (ambient, register), base⟩ =
      some ⟨some bodyLabel, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register) base) = _
  rw [atStart]
  simp [entry, TM2.stepAux]

theorem entryStep_radix_zero (q : ℕ) (hq : 0 < q) (radix : K)
    (startLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = entry q radix bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (hradix : base radix = encodeWord 0 ++ suffix)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some startLabel, (ambient, register), base⟩ =
      some ⟨some exitLabel, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register) base) = _
  rw [atStart]
  simp [entry, Nat.ne_of_gt hq, TM2.stepAux, hradix, encodeWord]

theorem entryStep_radix_positive (q n : ℕ) (hn : 0 < n) (radix : K)
    (startLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = entry q radix bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (hradix : base radix = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some startLabel, (ambient, register), base⟩ =
      some ⟨some bodyLabel, (ambient, none), base⟩ := by
  cases n with
  | zero => omega
  | succ n =>
    change some (TM2.stepAux (program startLabel) (ambient, register) base) = _
    rw [atStart]
    by_cases hq : q = 0 <;>
      simp [entry, hq, TM2.stepAux, hradix, encodeWord, List.replicate_succ]

namespace Control

/-- Two labels per coordinate, plus start, body, and exit labels. -/
abbrev Label (q : ℕ) := Fin q ⊕ (Fin q ⊕ Option Bool)

def start (q : ℕ) : Label q := .inr (.inr none)
def body (q : ℕ) : Label q := .inr (.inr (some false))
def exit (q : ℕ) : Label q := .inr (.inr (some true))
def check {q : ℕ} (i : Fin q) : Label q := .inl i
def resetLabel {q : ℕ} (i : Fin q) : Label q := .inr (.inl i)

def carry {q : ℕ} (i : Fin q) : Label q :=
  if h : i.val + 1 < q then check ⟨i.val + 1, h⟩ else exit q

/-- A fixed finite controller. Its only unspecified instruction is the
emitter body, whose actual leaf traces are supplied to `NestedCycle`. -/
def program (q : ℕ) (current remaining : Fin q → K) (radix : K)
    (emitter : TM2.Stmt (Alphabet (K := K)) (Label q) (σ × Option Bool)) :
    Label q → TM2.Stmt (Alphabet (K := K)) (Label q) (σ × Option Bool)
  | .inl i => increment (current i) (remaining i) (body q) (resetLabel i)
  | .inr (.inl i) => reset (current i) (remaining i) (resetLabel i) (carry i)
  | .inr (.inr none) => entry q radix (body q) (exit q)
  | .inr (.inr (some false)) => emitter
  | .inr (.inr (some true)) => .halt

omit [DecidableEq K] in
theorem label_card (q : ℕ) : Fintype.card (Label q) = 2 * q + 3 := by
  simp [Label]
  omega

end Control

end MaxCutGames.Foundations.Complexity.MachineTupleOdometer

end OAI
