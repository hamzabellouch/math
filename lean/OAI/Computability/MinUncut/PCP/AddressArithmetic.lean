import Mathlib
import OAI.Computability.MinUncut.PCP.ContextLoad
import OAI.Computability.MinUncut.Machines.MachineUnaryAdd

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceAddressArithmetic

open scoped BigOperators
open Target SourceContexts SourceOccurrences

theorem variable_rank (F : Formula) (u : ℕ) (v : VariableContext F u) :
    ((variableEncoding F u).code v).val =
      ∑ t : Fin u, (v t).val * F.«variables» ^ t.val := rfl

theorem clause_rank (F : Formula) (u : ℕ) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val =
      ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val := rfl

theorem left_address (F : Formula) (u : ℕ) (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ((variableEncoding F u).code v).val := rfl

theorem right_address (F : Formula) (u : ℕ) (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.«variables» ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val) := rfl

theorem dummy_address (F : Formula) (u : ℕ) :
    (dummyIndex F u).val =
      F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u) := by
  change F.«variables» ^ u * 2 ^ (2 ^ u) +
    (F.clauses.length ^ u * 2 ^ (8 ^ u) + 0) = _
  omega

theorem left_address_radix (F : Formula) (u : ℕ)
    (v : VariableContext F u) (f : Cube (I u)) :
    ((proofEncoding F u).code (.inl (v, f))).val =
      (((iEncoding u).function Encoding.bool).code f).val +
        2 ^ (2 ^ u) * ∑ t : Fin u, (v t).val * F.«variables» ^ t.val := by
  rw [left_address, variable_rank]

theorem right_address_radix (F : Formula) (u : ℕ)
    (c : ClauseContext F u) (g : Cube (J u)) :
    ((proofEncoding F u).code (.inr (.inl (c, g)))).val =
      F.«variables» ^ u * 2 ^ (2 ^ u) +
        ((((jEncoding u).function Encoding.bool).code g).val +
          2 ^ (8 ^ u) * ∑ t : Fin u, (c t).val * F.clauses.length ^ t.val) := by
  rw [right_address, clause_rank]

theorem nBits_eq_dummy_succ (F : Formula) (u : ℕ) :
    nBits F u = (dummyIndex F u).val + 1 := by
  rw [dummy_address, nBits_eq]
  omega

end MinUncutGames.Foundations.Hastad.SourceAddressArithmetic

namespace MinUncutGames.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

def rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) : Nat :=
  ∑ i : Fin width, digits i * radix ^ i.val

def reverseDigits {width : Nat} (digits : Fin width → Nat) (i : Nat) : Nat :=
  if h : i < width then digits (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_apply {width : Nat} (digits : Fin width → Nat) (i : Fin width) :
    reverseDigits digits i.val = digits i.rev := by
  simp [reverseDigits, i.isLt]

theorem horner_value_sum (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    MachineHorner.value radix digits n =
      ∑ i ∈ Finset.range n, digits i * radix ^ (n - 1 - i) := by
  induction n with
  | zero => simp [MachineHorner.value]
  | succ n ih =>
    rw [MachineHorner.value, ih, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n - i = (n - 1 - i) + 1 by omega, pow_succ]
    ac_rfl

theorem horner_reverse_eq_rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) :
    MachineHorner.value radix (reverseDigits digits) width = rank radix digits := by
  rw [horner_value_sum, Finset.sum_range]
  calc
    (∑ i : Fin width, reverseDigits digits i.val * radix ^ (width - 1 - i.val)) =
        ∑ i : Fin width, digits i.rev * radix ^ i.rev.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [reverseDigits_apply]
      have he : width - 1 - i.val = i.rev.val := by
        simp only [Fin.rev]
        omega
      rw [he]
    _ = rank radix digits := by
      simpa only [rank, Fin.revPerm_apply] using
        Equiv.sum_comp (Fin.revPerm (n := width)) (fun i => digits i * radix ^ i.val)

variable {K Λ σ : Type} {width : Nat}

def reverseSlots (slots : MachineHorner.Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  (Equiv.sumCongr (Equiv.refl (Fin 6)) (Fin.revPerm (n := width))).toEmbedding.trans slots

@[simp] theorem reverseSlots_control (slots : MachineHorner.Layout width ↪ K) (i : Fin 6) :
    reverseSlots slots (.inl i) = slots (.inl i) := rfl

@[simp] theorem reverseSlots_digit (slots : MachineHorner.Layout width ↪ K) (i : Fin width) :
    reverseSlots slots (.inr i) = slots (.inr i.rev) := rfl

variable [DecidableEq K]

omit [DecidableEq K] in
theorem clean_reverseSlots (slots : MachineHorner.Layout width ↪ K) (base : K → List Bool)
    (clean : MachineHorner.Clean slots base) : MachineHorner.Clean (reverseSlots slots) base where
  accA := by simpa only [reverseSlots_control] using clean.accA
  accB := by simpa only [reverseSlots_control] using clean.accB
  counter := by simpa only [reverseSlots_control] using clean.counter
  scratch := by simpa only [reverseSlots_control] using clean.scratch

def statement (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineHorner.statement (reverseSlots slots) labels exit

def program (slots : MachineHorner.Layout width ↪ K) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool)
      (MachineHorner.Label width) (MachineHorner.State σ) :=
  statement slots id none

theorem rankTrace (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      MachineHorner.steps radix (reverseDigits digits) width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩ := by
  have h := MachineHorner.hornerTrace (reverseSlots slots) labels exit p atLabels base radix
    (reverseDigits digits) operandRadix
    (fun i => by simpa only [reverseSlots_digit, reverseDigits_apply] using operandDigits i.rev)
    (clean_reverseSlots slots base clean) ambient register
  rw [horner_reverse_eq_rank] at h
  simpa only [MachineHorner.resultTapes, reverseSlots_control] using h

def rankInTime (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩)
      (MachineHorner.steps radix (reverseDigits digits) width) where
  steps := MachineHorner.steps radix (reverseDigits digits) width
  evals_in_steps := rankTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient register
  steps_le_m := Nat.le_refl _

def rankInPolynomialTime (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool)
    (magnitude : Nat) (radixBound : radix ≤ magnitude) (digitBound : ∀ i, digits i ≤ magnitude) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩)
      ((MachineHorner.timePolynomial width).eval magnitude) where
  steps := MachineHorner.steps radix (reverseDigits digits) width
  evals_in_steps := rankTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient register
  steps_le_m := MachineHorner.steps_le_timePolynomial radix (reverseDigits digits) width magnitude
    radixBound (fun i hi => by simpa only [reverseDigits, dite_eq_left hi] using digitBound (Fin.rev ⟨i, hi⟩))

def variableRankInTime (F : Formula) (u : Nat) (v : VariableContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.«variables»)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (v i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((variableEncoding F u).code v).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.«variables» (fun i => (v i).val)
    operandRadix operandDigits clean ambient register F.«variables» (Nat.le_refl _) (fun i => (v i).isLt.le)
  simpa only [rank, ← variable_rank F u v] using h

def clauseRankInTime (F : Formula) (u : Nat) (c : ClauseContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.clauses.length)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (c i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.clauses.length (fun i => (c i).val)
    operandRadix operandDigits clean ambient register F.clauses.length (Nat.le_refl _) (fun i => (c i).isLt.le)
  simpa only [rank, ← clause_rank F u c] using h

def programInTime (slots : MachineHorner.Layout width ↪ K)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots))
      ⟨some .start, ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩)
      (MachineHorner.steps radix (reverseDigits digits) width) :=
  rankInTime slots id none (program slots) (fun _ => rfl) base radix digits operandRadix
    operandDigits clean ambient register

def machine (width : Nat) : FinTM2 where
  K := MachineHorner.Layout width
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := MachineHorner.Label width
  main := .start
  σ := MachineHorner.State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (MachineHorner.Layout width))

def machineInTime (width radix : Nat) (digits : Fin width → Nat)
    (base : MachineHorner.Layout width → List Bool)
    (operandRadix : base (.inl 0) = encodeWord radix)
    (operandDigits : ∀ i, base (.inr i) = encodeWord (digits i))
    (clean : MachineHorner.Clean (Function.Embedding.refl _) base) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine width).step
      ⟨some (MachineHorner.Label.start), (((), ()), register), base⟩
      (some ⟨none, (((), ()), none),
        MachineHorner.resultTapes (Function.Embedding.refl _) base (rank radix digits)⟩)
      (MachineHorner.steps radix (reverseDigits digits) width) :=
  programInTime (Function.Embedding.refl _) base radix digits operandRadix operandDigits clean () register

variable {u : Nat} {Extra : Type}

def clauseSlots (controls : Fin 6 ↪ Extra) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => .current i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.current.inj h)

def variableSlots (controls : Fin 6 ↪ Extra) (selected : SlotContext u) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => SourceContextLoad.variableField i (slotEncoding.code (selected i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.field.inj h).1

@[simp] theorem clauseSlots_control (controls : Fin 6 ↪ Extra) (i : Fin 6) :
    clauseSlots (u := u) controls (.inl i) = .extra (controls i) := rfl

@[simp] theorem clauseSlots_digit (controls : Fin 6 ↪ Extra) (i : Fin u) :
    clauseSlots controls (.inr i) = .current i := rfl

@[simp] theorem variableSlots_control (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin 6) :
    variableSlots controls selected (.inl i) = .extra (controls i) := rfl

@[simp] theorem variableSlots_digit (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin u) :
    variableSlots controls selected (.inr i) =
      SourceContextLoad.variableField i (slotEncoding.code (selected i)) := rfl

theorem selectedDigits_loaded (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (controls : Fin 6 ↪ Extra) (base : SourceContextLoad.Tape u Extra → List Bool)
    (empty : ∀ i, base (SourceContextLoad.variableField i (slotEncoding.code (selected i))) = [])
    (i : Fin u) :
    SourceContextLoad.stageTapes F c base u (variableSlots controls selected (.inr i)) =
      encodeWord (sampledVariables F c selected i).val := by
  rw [variableSlots_digit]
  erw [SourceContextLoad.output_variable, empty i, List.append_nil]
  congr 1
  cases hs : selected i <;> simp [sampledVariables, PCP.nameAt, PCP.clauseAt, slotEncoding, hs] <;> rfl

end MinUncutGames.Foundations.Hastad.SourceRankPhase

namespace MinUncutGames.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open MinUncutGames.Reduction.CloneGap

abbrev Descriptor := Fin 3 × ℕ

def descriptor (u : ℕ) : LocalKey u → Descriptor
  | .inl f => (0, (((iEncoding u).function Encoding.bool).code f).val)
  | .inr (.inl g) => (1, (((jEncoding u).function Encoding.bool).code g).val)
  | .inr (.inr _) => (2, 0)

def baseValue (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) : ℕ :=
  if side = 0 then 2 ^ (2 ^ u) * ((variableEncoding F u).code v).val
  else if side = 1 then F.«variables» ^ u * 2 ^ (2 ^ u) +
    2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val
  else F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u)

def realize (base : Fin 3 → ℕ) (d : Descriptor) : ℕ := d.2 + base d.1

def words (base : Fin 3 → ℕ) (e : Equation Descriptor) : List ℕ :=
  [realize base e.first, realize base e.second, realize base e.third,
    if e.rhs then 1 else 0]

theorem realize_descriptor (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (key : LocalKey u) :
    realize (baseValue F u c v) (descriptor u key) = (addressMap F u c v key).val := by
  cases key with
  | inl f =>
      simpa [realize, descriptor, baseValue, addressMap] using
        (left_address F u v f).symm
  | inr key =>
      cases key with
      | inl g =>
          simp [realize, descriptor, baseValue, addressMap, right_address]
          omega
      | inr _dummy =>
          simp only [realize, descriptor, baseValue, show (2 : Fin 3) ≠ 0 by decide,
            show (2 : Fin 3) ≠ 1 by decide, ite_false, Nat.zero_add, addressMap,
            dummy_address]

theorem descriptor_offset_bound (u : ℕ) (key : LocalKey u) :
    (descriptor u key).2 < 2 ^ (2 ^ u) + 2 ^ (8 ^ u) + 1 := by
  cases key with
  | inl f =>
      have h := (((iEncoding u).function Encoding.bool).code f).isLt
      change _ < 2 ^ (2 ^ u) at h
      change (((iEncoding u).function Encoding.bool).code f).val < _
      calc
        _ < (2 ^ (2 ^ u) : ℕ) := h
        _ ≤ 2 ^ (2 ^ u) + 2 ^ (8 ^ u) := Nat.le_add_right _ _
        _ ≤ _ := Nat.le_add_right _ _
  | inr key =>
      cases key with
      | inl g =>
          have h := (((jEncoding u).function Encoding.bool).code g).isLt
          change _ < 2 ^ (8 ^ u) at h
          change (((jEncoding u).function Encoding.bool).code g).val < _
          calc
            _ < (2 ^ (8 ^ u) : ℕ) := h
            _ ≤ 2 ^ (2 ^ u) + 2 ^ (8 ^ u) := Nat.le_add_left _ _
            _ ≤ _ := Nat.le_add_right _ _
      | inr _dummy => simp [descriptor]

theorem sourceEquation_numeric (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    mapEquation Fin.val (sourceEquation F u D p) =
      mapEquation (realize (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2)))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit, mapEquation_comp, mapEquation_comp]
  congr 1
  funext key
  exact (realize_descriptor F u p.1.1 (sampledVariables F p.1.1 p.1.2) key).symm

theorem sourceEquation_words (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    MinUncutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [MinUncutGames.Reduction.SourceEncoding.equationWords, words, mapEquation]
  rw [realize_descriptor, realize_descriptor, realize_descriptor]
  rfl

theorem baseValue_lt (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) :
    baseValue F u c v side < nBits F u := by
  have hside : side = 0 ∨ side = 1 ∨ side = 2 := by omega
  rcases hside with rfl | rfl | rfl
  · have h := (addressMap F u c v (.inl (fun _ => false))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 0 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inl (fun _ => false)))).isLt
    rw [← realize_descriptor] at h
    change _ + baseValue F u c v 1 < _ at h
    exact (Nat.le_add_left _ _).trans_lt h
  · have h := (addressMap F u c v (.inr (.inr ()))).isLt
    rw [← realize_descriptor] at h
    simpa only [realize, descriptor, Nat.zero_add] using h

theorem equation_emit_steps_le (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (e : Equation Descriptor) :
    2 * (baseValue F u c v e.first.1 + baseValue F u c v e.second.1 +
      baseValue F u c v e.third.1) + 16 ≤ 6 * nBits F u + 16 := by
  have h₁ := (baseValue_lt F u c v e.first.1).le
  have h₂ := (baseValue_lt F u c v e.second.1).le
  have h₃ := (baseValue_lt F u c v e.third.1).le
  omega

end MinUncutGames.Foundations.Hastad.SourceAddressDescriptors

end OAI
