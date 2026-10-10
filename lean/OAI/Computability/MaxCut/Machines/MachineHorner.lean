import Mathlib
import OAI.Computability.MaxCut.Machines.MachineUnaryMultiply

namespace OAI

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Layout (width : Nat) := Fin 6 ⊕ Fin width
abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineRadixStep.State σ

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

def accumulator (flip : Bool) : Fin 6 := if flip then 2 else 1

@[simp] theorem accumulator_ne (flip : Bool) : accumulator flip ≠ accumulator (!flip) := by
  cases flip <;> decide

def radixLayout (flip : Bool) (i : Fin width) : Fin 6 ↪ Layout width where
  toFun
    | 0 => .inl 0
    | 1 => .inl (accumulator flip)
    | 2 => .inr i
    | 3 => .inl (accumulator (!flip))
    | 4 => .inl 4
    | 5 => .inl 5
  inj' := by
    intro a b h
    cases flip <;> fin_cases a <;> fin_cases b <;> simp [accumulator] at h ⊢

def radixSlots (slots : Layout width ↪ K) (i : Fin width) : Fin 6 ↪ K :=
  (radixLayout (parity i.val) i).trans slots

@[simp] theorem radixSlots_base (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 0 = slots (.inl 0) := rfl
@[simp] theorem radixSlots_acc (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 1 = slots (.inl (accumulator (parity i.val))) := rfl
@[simp] theorem radixSlots_digit (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 2 = slots (.inr i) := rfl
@[simp] theorem radixSlots_out (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 3 = slots (.inl (accumulator (parity (i.val + 1)))) := rfl
@[simp] theorem radixSlots_counter (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 4 = slots (.inl 4) := rfl
@[simp] theorem radixSlots_scratch (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 5 = slots (.inl 5) := rfl

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

/-- Consume an isolated unary field, including its delimiter. -/
def drainLoop (tape : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .pop tape (fun state bit => (state.1, bit))
    (.branch (fun state => state.2.getD false)
      (.goto fun _ => loopLabel)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt tape exit)))

variable [DecidableEq K]

def statement (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots (.inl 1)) (fun _ => false)
      (.load (fun state => (state.1, none)) (.goto fun _ => labels (entryLabel width 0)))
  | .radix i inner => MachineRadixStep.statement (radixSlots slots i)
      (fun l => labels (.radix i l)) (some (labels (.clear i))) inner
  | .clear i => drainLoop (slots (.inl (accumulator (parity i.val))))
      (labels (.clear i)) (some (labels (entryLabel width (i.val + 1))))
  | .finishDrain => Reduction.MachineTransfer.loopAt
      (slots (.inl (accumulator (parity width)))) (slots (.inl 5)) id false
      (labels .finishDrain) (some (labels .finishRestore))
  | .finishRestore => Reduction.MachineTransfer.loopAt (slots (.inl 5)) (slots (.inl 3)) id false
      (labels .finishRestore) exit

def program (slots : Layout width ↪ K) :
    Label width → TM2.Stmt (Alphabet (K := K)) (Label width) (State σ) := statement slots id none

def machine (width : Nat) : FinTM2 where
  K := Layout width
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := Label width
  main := .start
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Layout width))

def value (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => radix * value radix digits n + digits n

def stepCost (radix acc digit : Nat) : Nat :=
  MachineRadixStep.steps radix acc digit + acc + 1

def prefixSteps (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n)

def stageTapes (slots : Layout width ↪ K) (base : K → List Bool) (n acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl (accumulator (parity n)))) (encodeWord acc)

def resultTapes (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl 3)) (encodeWord acc ++ base (slots (.inl 3)))

theorem drainTrace (tape : K) (loopLabel : Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLoop : p loopLabel = drainLoop tape loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[n + 1]
      (some ⟨some loopLabel, ((ambient, ()), register),
        Function.update base tape (encodeWord n ++ suffix)⟩) =
      some ⟨exit, ((ambient, ()), none), Function.update base tape suffix⟩ := by
  induction n generalizing register with
  | zero =>
    change some (TM2.stepAux (p loopLabel) _ _) = _
    rw [atLoop]
    cases exit <;> simp [drainLoop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[n + 1]
      (some (TM2.stepAux (p loopLabel) _ _)) = _
    rw [atLoop]
    simp only [drainLoop, TM2.stepAux, Function.update_self, encodeWord,
      List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
      Option.getD_some, Function.update_idem]
    exact ih (some true)

structure Clean (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  accA : base (slots (.inl 1)) = []
  accB : base (slots (.inl 2)) = []
  counter : base (slots (.inl 4)) = []
  scratch : base (slots (.inl 5)) = []

omit [DecidableEq K] in
theorem Clean.acc {slots : Layout width ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (flip : Bool) : base (slots (.inl (accumulator flip))) = [] := by
  cases flip
  · exact clean.accA
  · exact clean.accB

/-- One genuine radix execution followed by a unary drain of its old input
accumulator. The new accumulator is left in the alternate physical tape. -/
theorem digitTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : Nat) (i : Fin width)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigit : base (slots (.inr i)) = encodeWord digit)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[stepCost radix acc digit]
      (some ⟨some (labels (.radix i (.multiply .copyDrain))), ((ambient, ()), register),
        stageTapes slots base i.val acc⟩) =
      some ⟨some (labels (entryLabel width (i.val + 1))), ((ambient, ()), none),
        stageTapes slots base (i.val + 1) (radix * acc + digit)⟩ := by
  let rs := radixSlots slots i
  let before := stageTapes slots base i.val acc
  let after := MachineRadixStep.resultTapes rs before (radix * acc + digit)
  have h01 : rs 0 ≠ rs 1 := rs.injective.ne (by decide)
  have h21 : rs 2 ≠ rs 1 := rs.injective.ne (by decide)
  have h31 : rs 3 ≠ rs 1 := rs.injective.ne (by decide)
  have h41 : rs 4 ≠ rs 1 := rs.injective.ne (by decide)
  have h51 : rs 5 ≠ rs 1 := rs.injective.ne (by decide)
  have hb : before (rs 0) = encodeWord radix := by
    change Function.update base (rs 1) (encodeWord acc) (rs 0) = _
    rw [Function.update_of_ne h01]
    exact operandRadix
  have ha : before (rs 1) = encodeWord acc := by
    exact Function.update_self _ _ _
  have hd : before (rs 2) = encodeWord digit := by
    change Function.update base (rs 1) (encodeWord acc) (rs 2) = _
    rw [Function.update_of_ne h21]
    exact operandDigit
  have hc : before (rs 4) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 4) = _
    rw [Function.update_of_ne h41]
    exact clean.counter
  have hs : before (rs 5) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 5) = _
    rw [Function.update_of_ne h51]
    exact clean.scratch
  have hout : before (rs 3) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 3) = _
    rw [Function.update_of_ne h31]
    exact clean.acc _
  have hradix := MachineRadixStep.radixStepTrace rs (fun l => labels (.radix i l))
    (some (labels (.clear i))) p (fun l => atLabels (.radix i l)) before radix acc digit
    hb ha hd hc hs ambient register
  have hold : after (rs 1) = encodeWord acc := by
    change Function.update before (rs 3) _ (rs 1) = _
    rw [Function.update_of_ne (Ne.symm h31), ha]
  have hstart : Function.update after (rs 1) (encodeWord acc ++ []) = after := by
    rw [List.append_nil, ← hold, Function.update_eq_self]
  have hfinish : Function.update after (rs 1) [] =
      stageTapes slots base (i.val + 1) (radix * acc + digit) := by
    have hempty : base (rs 1) = [] := clean.acc _
    change Function.update (Function.update (Function.update base (rs 1) (encodeWord acc))
      (rs 3) (encodeWord (radix * acc + digit) ++ before (rs 3))) (rs 1) [] =
      Function.update base (rs 3) (encodeWord (radix * acc + digit))
    rw [hout, List.append_nil]
    funext k
    by_cases h1 : k = rs 1
    · subst k; simp [Ne.symm h31, hempty]
    · by_cases h3 : k = rs 3
      · subst k; simp [h31]
      · simp [h1, h3]
  have hdrain := drainTrace (rs 1) (labels (.clear i))
    (some (labels (entryLabel width (i.val + 1)))) p (atLabels (.clear i))
    after acc [] ambient none
  rw [hstart, hfinish] at hdrain
  rw [show stepCost radix acc digit = (acc + 1) + MachineRadixStep.steps radix acc digit by
    unfold stepCost; omega, Function.iterate_add_apply, hradix]
  exact hdrain

/-- Prefix induction follows the fixed finite sequence of digit labels. -/
theorem prefixTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (n : Nat) (hn : n ≤ width) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps radix digits n]
      (some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩) =
      some ⟨some (labels (entryLabel width n)), ((ambient, ()), none),
        stageTapes slots base n (value radix digits n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < width := by omega
    let i : Fin width := ⟨n, hlt⟩
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    have h := digitTrace slots labels exit p atLabels base radix (value radix digits n)
      (digits n) i operandRadix (operandDigits i) clean ambient none
    simpa only [entryLabel, dite_eq_left hlt, i, value] using h

/-- Move the final accumulator to the external output, restoring its order and
emptying accumulator/scratch. The old destination is retained as a suffix. -/
theorem finishTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (acc : Nat) (clean : Clean slots base) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[2 * acc + 4]
      (some ⟨some (labels .finishDrain), ((ambient, ()), none), stageTapes slots base width acc⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ := by
  let src := slots (.inl (accumulator (parity width)))
  let scratch := slots (.inl 5)
  let dst := slots (.inl 3)
  have hsrcScratch : src ≠ scratch := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hsrcDst : src ≠ dst := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hscratchDst : scratch ≠ dst := slots.injective.ne (by simp)
  have hsrc : base src = [] := clean.acc _
  have hs : base scratch = [] := clean.scratch
  let before := stageTapes slots base width acc
  let middle := Function.update base scratch (encodeWord acc).reverse
  have hinput : before src = encodeWord acc := Function.update_self _ _ _
  have hscratch : before scratch = [] := by
    change Function.update base src (encodeWord acc) scratch = []
    rw [Function.update_of_ne (Ne.symm hsrcScratch), hs]
  have hfirstTapes : Reduction.MachineTransfer.tapesAt src scratch before []
      ((before src).reverse.map id ++ before scratch) = middle := by
    rw [hinput, hscratch, List.append_nil, List.map_id]
    funext k
    by_cases h1 : k = src
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, middle, hsrcScratch, hsrc]
    · by_cases h2 : k = scratch
      · subst k; simp [Reduction.MachineTransfer.tapesAt, middle]
      · simp [Reduction.MachineTransfer.tapesAt, middle, before, stageTapes, h1, h2, src]
  have first := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) src scratch hsrcScratch id false
    (labels .finishDrain) (some (labels .finishRestore)) p (atLabels .finishDrain)
    before (ambient, ()) none
  rw [hfirstTapes] at first
  have hlength : (before src).length + 1 = acc + 2 := by
    simp [hinput, encodeWord, Nat.add_assoc]
  rw [hlength] at first
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishDrain), ((ambient, ()), none), before⟩) =
      some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩ at first
  have hmSource : middle scratch = (encodeWord acc).reverse := Function.update_self _ _ _
  have hmOutput : middle dst = base dst := by
    exact Function.update_of_ne (Ne.symm hscratchDst) _ _
  have hsecondTapes : Reduction.MachineTransfer.tapesAt scratch dst middle []
      ((middle scratch).reverse.map id ++ middle dst) = resultTapes slots base acc := by
    rw [hmSource, hmOutput, List.reverse_reverse, List.map_id]
    funext k
    by_cases h1 : k = dst
    · subst k; simp [Reduction.MachineTransfer.tapesAt, resultTapes, dst]
    · by_cases h2 : k = scratch
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, hscratchDst, hs, scratch, dst]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, h1, h2, dst]
  have second := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) scratch dst hscratchDst id false
    (labels .finishRestore) exit p (atLabels .finishRestore) middle (ambient, ()) none
  rw [hsecondTapes] at second
  have hmLength : (middle scratch).length + 1 = acc + 2 := by
    simp [hmSource, encodeWord, Nat.add_assoc]
  rw [hmLength] at second
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ at second
  rw [show 2 * acc + 4 = (acc + 2) + (acc + 2) by omega,
    Function.iterate_add_apply, first]
  exact second

def steps (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  prefixSteps radix digits width + 2 * value radix digits width + 5

/-- Complete actual Horner execution on preserved digit/base fields. Initial
work tapes are empty; only the destination changes at the optional continuation. -/
theorem hornerTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix digits width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩ := by
  have start : TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩ =
      some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩ := by
    change some (TM2.stepAux (p (labels .start)) _ _) = _
    rw [atLabels .start]
    simp only [statement, TM2.stepAux, clean.accA, stageTapes, parity, accumulator,
      Bool.false_eq_true, ↓reduceIte, encodeWord, List.replicate_zero, List.nil_append]
  have prefixRun := prefixTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient width (Nat.le_refl _)
  have final := finishTrace slots labels exit p atLabels base (value radix digits width) clean ambient
  have hend : entryLabel width width = .finishDrain := by simp [entryLabel]
  rw [hend] at prefixRun
  rw [show steps radix digits width =
    ((2 * value radix digits width + 4) + prefixSteps radix digits width) + 1 by
      unfold steps; omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    (2 * value radix digits width + 4) + prefixSteps radix digits width]
      (TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩) = _
  rw [start, Function.iterate_add_apply, prefixRun]
  exact final

omit [DecidableEq K] in
theorem value_eq_foldl (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    value radix digits n =
      ((List.range n).map digits).foldl (fun acc digit => radix * acc + digit) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, ← ih]

omit [DecidableEq K] in
/-- A magnitude bound accommodates arbitrary digits, including fixed polynomial
coefficients larger than the radix. No bounded-digit assumption is needed for
execution correctness. -/
theorem value_add_one_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n + 1 ≤ (magnitude + 1) ^ n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    have hn' : n < width := by omega
    have hm := Nat.mul_le_mul_right (value radix digits n) radixBound
    calc
      value radix digits (n + 1) + 1 ≤ (magnitude + 1) * (value radix digits n + 1) := by
        rw [value]
        have hd := digitBound n hn'
        nlinarith
      _ ≤ (magnitude + 1) * (magnitude + 1) ^ n :=
        Nat.mul_le_mul_left _ (ih (by omega))
      _ = (magnitude + 1) ^ (n + 1) := by rw [pow_succ]; ac_rfl

omit [DecidableEq K] in
theorem value_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n ≤ (magnitude + 1) ^ width := by
  have h := value_add_one_le radix digits width magnitude radixBound digitBound n hn
  exact (Nat.le_trans (Nat.le_add_right _ _) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) hn)

def perDigitBound (width magnitude : Nat) : Nat :=
  3 * magnitude * (magnitude + 1) ^ width + 9 * (magnitude + 1) ^ width + 3 * magnitude + 14

omit [DecidableEq K] in
theorem stepCost_le (radix acc digit width magnitude : Nat)
    (radixBound : radix ≤ magnitude) (accBound : acc ≤ (magnitude + 1) ^ width)
    (digitBound : digit ≤ magnitude) :
    stepCost radix acc digit ≤ perDigitBound width magnitude := by
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 3 radixBound) accBound
  unfold stepCost MachineRadixStep.steps perDigitBound
  omega

omit [DecidableEq K] in
theorem prefixSteps_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) :
    prefixSteps radix digits n ≤ n * perDigitBound width magnitude := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hn' : n < width := by omega
    have ha := value_le radix digits width magnitude radixBound digitBound n (by omega)
    have hc := stepCost_le radix (value radix digits n) (digits n) width magnitude
      radixBound ha (digitBound n hn')
    rw [prefixSteps]
    calc
      prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n) ≤
          n * perDigitBound width magnitude + perDigitBound width magnitude :=
        Nat.add_le_add (ih (by omega)) hc
      _ = (n + 1) * perDigitBound width magnitude := by rw [Nat.add_mul, Nat.one_mul]

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width *
    (3 * Polynomial.X * (Polynomial.X + 1) ^ width +
      9 * (Polynomial.X + 1) ^ width + 3 * Polynomial.X + 14) +
    2 * (Polynomial.X + 1) ^ width + 5

omit [DecidableEq K] in
@[simp] theorem timePolynomial_eval (width magnitude : Nat) :
    (timePolynomial width).eval magnitude =
      width * perDigitBound width magnitude + 2 * (magnitude + 1) ^ width + 5 := by
  simp [timePolynomial, perDigitBound]

omit [DecidableEq K] in
theorem steps_le_timePolynomial (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    steps radix digits width ≤ (timePolynomial width).eval magnitude := by
  have hp := prefixSteps_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have hv := value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  rw [timePolynomial_eval]
  unfold steps
  omega

def hornerInTime (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩)
      (steps radix digits width) where
  steps := steps radix digits width
  evals_in_steps := hornerTrace slots labels exit p atLabels base radix digits
    operandRadix operandDigits clean ambient register
  steps_le_m := Nat.le_refl _

def hornerInPolynomialTime (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) (magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩)
      ((timePolynomial width).eval magnitude) where
  steps := steps radix digits width
  evals_in_steps := hornerTrace slots labels exit p atLabels base radix digits
    operandRadix operandDigits clean ambient register
  steps_le_m := steps_le_timePolynomial radix digits width magnitude radixBound digitBound

open scoped BigOperators

/-- The actual total bit length of the isolated radix and digit fields. -/
def operandLength (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  (encodeWord radix).length + ∑ i ∈ Finset.range width, (encodeWord (digits i)).length

omit [DecidableEq K] in
theorem radix_le_operandLength (radix : Nat) (digits : Nat → Nat) (width : Nat) :
    radix ≤ operandLength radix digits width := by
  unfold operandLength
  simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
  omega

omit [DecidableEq K] in
theorem digit_le_operandLength (radix : Nat) (digits : Nat → Nat) (width i : Nat)
    (hi : i < width) : digits i ≤ operandLength radix digits width := by
  have h : (encodeWord (digits i)).length ≤
      ∑ j ∈ Finset.range width, (encodeWord (digits j)).length :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((encodeWord (digits j)).length))
      (Finset.mem_range.mpr hi)
  have hlen : digits i + 1 ≤ ∑ j ∈ Finset.range width, (encodeWord (digits j)).length := by
    simpa only [encodeWord, List.length_append, List.length_replicate, List.length_singleton] using h
  unfold operandLength
  omega

@[simp] theorem resultTapes_output (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) :
    resultTapes slots base acc (slots (.inl 3)) = encodeWord acc ++ base (slots (.inl 3)) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat)
    (k : K) (hk : k ≠ slots (.inl 3)) : resultTapes slots base acc k = base k := by
  simp [resultTapes, hk]

/-- Actual subroutine time bounded in the concrete lengths of its operand
fields. The destination suffix and unrelated tapes are preserved without scans. -/
def hornerInEncodedPolynomialTime (slots : Layout width ↪ K) (labels : Label width → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩)
      ((timePolynomial width).eval (operandLength radix digits width)) :=
  hornerInPolynomialTime slots labels exit p atLabels base radix digits operandRadix operandDigits
    clean ambient register (operandLength radix digits width)
    (radix_le_operandLength radix digits width)
    (fun i hi => digit_le_operandLength radix digits width i hi)

end MaxCutGames.Foundations.Complexity.MachineHorner

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

namespace MaxCutGames.Explicit.MachineProductField

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

/-- Gather's table/query/scan/scratch and coordinate tapes; then radix, two
Horner accumulators, counter, scratch, isolated field output, global output. -/
abbrev Layout (width : Nat) := MachineProductGather.Tape width ⊕ Fin 7

def gatherSlots (slots : Layout width ↪ K) : MachineProductGather.Tape width ↪ K :=
  Function.Embedding.trans (Function.Embedding.inl) slots

def hornerRole : MachineHorner.Layout width → Layout width
  | .inl 0 => .inr 0
  | .inl 1 => .inr 1
  | .inl 2 => .inr 2
  | .inl 3 => .inr 5
  | .inl 4 => .inr 3
  | .inl 5 => .inr 4
  | .inr i => .inl (.inr (.inr i.rev))

theorem hornerRole_injective : Function.Injective (hornerRole (width := width)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [hornerRole]
    | inr b => fin_cases a <;> simp [hornerRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> simp [hornerRole] at h
    | inr b => simpa [hornerRole] using h

def hornerSlots (slots : Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  Function.Embedding.trans ⟨hornerRole, hornerRole_injective⟩ slots

def clearTapes (slots : Layout width ↪ K) : List K :=
  [slots (.inl (.inl 1)), slots (.inl (.inl 2))] ++
    List.ofFn (fun i : Fin width => slots (.inl (.inr (.inr i))))

abbrev Label (slots : Layout width ↪ K) :=
  MachineProductGather.Label width ⊕
    (MachineHorner.Label width ⊕ (Unit ⊕ MachineDrainMany.Label (clearTapes slots)))

def entry (slots : Layout width ↪ K) : Label slots :=
  .inl (MachineProductGather.entry width)

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (offsets : Fin width → Nat)
    (labels : Label slots → Λ) (exit : Option Λ) :
    Label slots → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineProductGather.instruction width (gatherSlots slots) coefficient offsets
      (fun x => labels (.inl x)) (some (labels (.inr (.inl .start)))) l
  | .inr (.inl l) => MachineHorner.statement (hornerSlots slots)
      (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ()))))) l
  | .inr (.inr (.inl _)) => loopAt (slots (.inr 5)) (slots (.inr 6)) id false
      (labels (.inr (.inr (.inl ()))))
      (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
  | .inr (.inr (.inr l)) => MachineDrainMany.instruction (clearTapes slots)
      (fun x => labels (.inr (.inr (.inr x)))) exit l

/-- Conditions on real input/work stacks; arbitrary output suffixes remain
permitted. The two query/scan tapes are empty at a row boundary. -/
structure Ready (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  query : base (slots (.inl (.inl 1))) = []
  scan : base (slots (.inl (.inl 2))) = []
  gatherScratch : base (slots (.inl (.inl 3))) = []
  fields : ∀ i, base (slots (.inl (.inr (.inr i)))) = []
  accA : base (slots (.inr 1)) = []
  accB : base (slots (.inr 2)) = []
  counter : base (slots (.inr 3)) = []
  hornerScratch : base (slots (.inr 4)) = []
  output : base (slots (.inr 5)) = []

def gathered (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) : K → List Bool :=
  MachineProductGather.finalTapes values coefficient width (gatherSlots slots)
    indices offsets fields base

def evaluated (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots)
    (gathered slots values coefficient indices offsets fields base) value

def emitted (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  tapesAt (slots (.inr 5)) (slots (.inr 6))
    (evaluated slots values coefficient indices offsets fields base value) []
    ((encodeWord value).reverse ++ base (slots (.inr 6)))

def finalTapes (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineDrainMany.finalTapes (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)

def steps (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (radix : Nat) (digits : Nat → Nat) : Nat :=
  MachineProductGather.steps values coefficient width indices offsets +
    MachineHorner.steps radix digits width + (MachineHorner.value radix digits width + 2) +
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base
        (MachineHorner.value radix digits width))

theorem gathered_extra (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin 7) :
    gathered slots values coefficient indices offsets fields base (slots (.inr i)) =
      base (slots (.inr i)) := by
  apply MachineProductGather.finalTapes_other
  · apply slots.injective.ne; simp []
  · apply slots.injective.ne; simp []
  · intro j; apply slots.injective.ne; simp []

/-- Actual execution of the complete gather/Horner/emit/cleanup phase. The
field equality connects only mathematical tape contents; all transition work
is proved from the concrete instructions. -/
theorem fieldTrace (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label slots → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool) (ready : Ready slots base)
    (tableWord : base (slots (.inl (.inl 0))) = encodeWords values)
    (sourceWords : ∀ i, base (slots (.inl (.inr (.inl i)))) =
      encodeWord (indices i) ++ suffixes i)
    (radix : Nat) (digits : Nat → Nat)
    (radixWord : base (slots (.inr 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin width, digits i.val = fields i.rev)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps slots values coefficient indices offsets fields base radix digits]
      (some ⟨some (labels (entry slots)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), finalTapes slots values coefficient indices offsets fields
        base (MachineHorner.value radix digits width)⟩ := by
  let middle := gathered slots values coefficient indices offsets fields base
  have gather := MachineProductGather.gatherTrace values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected (fun x => labels (.inl x))
    (some (labels (.inr (.inl .start)))) program (fun x => atLabels (.inl x))
    base suffixes tableWord ready.gatherScratch sourceWords (ambient, ()) register
  have preserved (i : Fin 7) : middle (slots (.inr i)) = base (slots (.inr i)) :=
    gathered_extra slots values coefficient indices offsets fields base i
  have middleRadix : middle (hornerSlots slots (.inl 0)) = encodeWord radix := by
    rw [show hornerSlots slots (.inl 0) = slots (.inr 0) from rfl, preserved]
    exact radixWord
  have middleDigits (i : Fin width) :
      middle (hornerSlots slots (.inr i)) = encodeWord (digits i.val) := by
    rw [show hornerSlots slots (.inr i) =
      gatherSlots slots (.inr (.inr i.rev)) from rfl]
    dsimp only [middle, gathered]
    rw [MachineProductGather.finalTapes_field values coefficient width (gatherSlots slots)
      (gatherSlots slots).injective indices offsets fields base i.rev]
    rw [show base (gatherSlots slots (.inr (.inr i.rev))) = [] from ready.fields i.rev,
      List.append_nil, digitWords i]
  have clean : MachineHorner.Clean (hornerSlots slots) middle := by
    constructor
    · change middle (slots (.inr 1)) = []; rw [preserved]; exact ready.accA
    · change middle (slots (.inr 2)) = []; rw [preserved]; exact ready.accB
    · change middle (slots (.inr 3)) = []; rw [preserved]; exact ready.counter
    · change middle (slots (.inr 4)) = []; rw [preserved]; exact ready.hornerScratch
  have horner := MachineHorner.hornerTrace (hornerSlots slots)
    (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ())))))
    program (fun x => atLabels (.inr (.inl x))) middle radix digits middleRadix
    middleDigits clean ambient none
  let value := MachineHorner.value radix digits width
  let after := evaluated slots values coefficient indices offsets fields base value
  have outputWord : after (slots (.inr 5)) = encodeWord value := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value
      (hornerSlots slots (.inl 3)) = _
    rw [MachineHorner.resultTapes_output]
    rw [show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
      preserved, ready.output, List.append_nil]
  have accWord : after (slots (.inr 6)) = base (slots (.inr 6)) := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value (slots (.inr 6)) = _
    rw [MachineHorner.resultTapes_other _ _ _ _ (slots.injective.ne (by simp [hornerRole])), preserved]
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inr 5)) (slots (.inr 6)) (slots.injective.ne (by simp [])) id false
    (labels (.inr (.inr (.inl ()))))
    (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
    program (atLabels (.inr (.inr (.inl ())))) after (ambient, ()) none
  rw [outputWord, accWord, List.map_id] at emit
  simp only [encodeWord_length] at emit
  have drain := MachineDrainMany.trace (clearTapes slots)
    (fun x => labels (.inr (.inr (.inr x)))) exit program
    (fun x => atLabels (.inr (.inr (.inr x))))
    (emitted slots values coefficient indices offsets fields base value) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none] at drain
  have emit' : (advance (TM2.step program))^[value + 2]
      (some ⟨some (labels (.inr (.inr (.inl ())))), ((ambient, ()), none), after⟩) =
      some ⟨MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit,
        ((ambient, ()), none), emitted slots values coefficient indices offsets fields base value⟩ := emit
  have compose {a b : Nat} {x y z : Option (TM2.Cfg (fun _ : K => Bool) Λ (MachineHorner.State σ))}
      (first : (advance (TM2.step program))^[a] x = y)
      (second : (advance (TM2.step program))^[b] y = z) :
      (advance (TM2.step program))^[a + b] x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, first, second]
  have gh := compose gather horner
  have ghe := compose gh emit'
  have whole := compose ghe drain
  simpa only [steps, value, entry, finalTapes] using whole

end MaxCutGames.Explicit.MachineProductField

end OAI
