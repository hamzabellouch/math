import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineLogCounter
import OAI.Computability.UniqueGames.Machines.MachineUnaryAffineAt

namespace OAI

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- A boundary test which inspects the first unary bit without consuming it. -/
def zeroTest (operand : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek operand (fun s head => (s.1, head))
    (.load (fun s => ((s.1.1, !(s.2.getD false)), none))
      (Reduction.MachineTransfer.exitAt operand exit))

theorem zeroTestTrace (operand : K) (testLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atTest : program testLabel = zeroTest operand exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (word : base operand = encodeWord n ++ suffix)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[1]
      (some ⟨some testLabel, ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (n = 0)), none), base⟩ := by
  change some (TM2.stepAux (program testLabel) _ _) = _
  rw [atTest]
  cases n <;> cases exit <;>
    simp [zeroTest, TM2.stepAux, word, encodeWord, List.replicate_succ,
      Reduction.MachineTransfer.exitAt]

/-- Slots 0 and 1 are the operands; slots 2 and 3 are their saved prefixes. -/
def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

@[simp] theorem transferLeft_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementLeft : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 2) (slots 0)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementLeft =
      tapes slots base replacementLeft right replacementSaved savedRight := by
  simp [Reduction.MachineTransfer.tapesAt]

@[simp] theorem transferRight_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementRight : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 3) (slots 1)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementRight =
      tapes slots base left replacementRight savedLeft replacementSaved := by
  simp [Reduction.MachineTransfer.tapesAt]

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

instance : Fintype Label where
  elems := { .scan, .restoreLeft, .restoreRight }
  complete l := by cases l <;> simp

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .scan => scan slots (labels .scan) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (slots 2) (slots 0) id false
      (labels .restoreLeft) (some (labels .restoreRight))
  | .restoreRight => Reduction.MachineTransfer.loopAt (slots 3) (slots 1) id false
      (labels .restoreRight) exit

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

theorem comparisonTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩ := by
  have hscan := scanTrace slots (labels .scan) (labels .restoreLeft) program (atLabels .scan)
    base a b leftSuffix rightSuffix [] [] ambient flag register
  simp only [List.append_nil] at hscan
  have hwordLeft : List.replicate (min a b) true ++ (encodeWord (a - b) ++ leftSuffix) =
      encodeWord a ++ leftSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (a - b) = a by omega]
  have hwordRight : List.replicate (min a b) true ++ (encodeWord (b - a) ++ rightSuffix) =
      encodeWord b ++ rightSuffix := by
    rw [MachineUnaryAffineAt.prepend_replicate_word,
      show min a b + (b - a) = b by omega]
  let middle := tapes slots base (encodeWord (a - b) ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) (List.replicate (min a b) true) (List.replicate (min a b) true)
  have hleft := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 2) (slots 0)
    (slots.injective.ne (by decide)) id false (labels .restoreLeft) (some (labels .restoreRight))
    program (by simpa only [statement] using atLabels .restoreLeft)
    middle (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(middle (slots 2)).length + 1]
    (some ⟨some (labels .restoreLeft), ((ambient, decide (a < b)), none), middle⟩) = _ at hleft
  simp only [middle, tapes_savedLeft, tapes_left, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordLeft, transferLeft_tapes] at hleft
  let afterLeft := tapes slots base (encodeWord a ++ leftSuffix)
    (encodeWord (b - a) ++ rightSuffix) [] (List.replicate (min a b) true)
  have hright := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Bool) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) id false (labels .restoreRight) exit
    program (by simpa only [statement] using atLabels .restoreRight)
    afterLeft (ambient, decide (a < b)) none
  change (advance (TM2.step program))^[(afterLeft (slots 3)).length + 1]
    (some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩) = _ at hright
  simp only [afterLeft, tapes_savedRight, tapes_right, List.length_replicate, List.reverse_replicate,
    List.map_id, hwordRight, transferRight_tapes] at hright
  have hfirst : (advance (TM2.step program))^[(min a b + 1) + (min a b + 1)]
      (some ⟨some (labels .scan), ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) [] []⟩) =
      some ⟨some (labels .restoreRight), ((ambient, decide (a < b)), none), afterLeft⟩ := by
    rw [Function.iterate_add_apply, hscan]
    exact hleft
  rw [show steps a b = (min a b + 1) + ((min a b + 1) + (min a b + 1)) by
    unfold steps; omega, Function.iterate_add_apply, hfirst]
  exact hright

/-- Actual comparison on a caller frame: both complete operand tapes and all
other tapes are preserved, both scratch tapes remain empty, and the finite
result flag is precisely the strict comparison of the two unary values. -/
theorem lessThanTrace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .scan), ((ambient, flag), register), base⟩) =
      some ⟨exit, ((ambient, decide (a < b)), none), base⟩ := by
  have h := comparisonTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    ambient flag register
  have hframe := tapes_self slots base
  rw [leftWord, rightWord, leftEmpty, rightEmpty] at hframe
  rw [hframe] at h
  exact h

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 3 * Polynomial.X + Polynomial.C 3

theorem steps_le_time (a b : Nat) : steps a b ≤ timePolynomial.eval (a + b) := by
  simp only [steps, timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have := Nat.min_le_left a b
  omega

def lessThanInPolynomialTime (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (slots 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (slots 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), ((ambient, flag), register), base⟩
      (some ⟨exit, ((ambient, decide (a < b)), none), base⟩) (timePolynomial.eval (a + b)) where
  steps := steps a b
  evals_in_steps := lessThanTrace slots labels exit program atLabels base a b leftSuffix rightSuffix
    leftWord rightWord leftEmpty rightEmpty ambient flag register
  steps_le_m := steps_le_time a b

abbrev machine : Turing.FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := .scan
  σ := State Unit
  initialState := (((), false), none)
  m := statement (Function.Embedding.refl _) id none

def machineInPolynomialTime (base : Fin 4 → List Bool) (a b : Nat)
    (leftSuffix rightSuffix : List Bool)
    (leftWord : base 0 = encodeWord a ++ leftSuffix)
    (rightWord : base 1 = encodeWord b ++ rightSuffix)
    (leftEmpty : base 2 = []) (rightEmpty : base 3 = []) :
    StateTransition.EvalsToInTime machine.step
      ⟨some .scan, (((), false), none), base⟩
      (some ⟨none, (((), decide (a < b)), none), base⟩) (timePolynomial.eval (a + b)) :=
  lessThanInPolynomialTime (Function.Embedding.refl _) id none machine.m (fun _ => rfl)
    base a b leftSuffix rightSuffix leftWord rightWord leftEmpty rightEmpty () false none

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryLessAt

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PCPIterationMachine

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

end UniqueGamesTheorem.Foundations.Complexity.PCPIterationMachine

end OAI
