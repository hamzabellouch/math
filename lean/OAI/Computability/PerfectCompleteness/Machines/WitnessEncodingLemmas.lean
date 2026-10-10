import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import OAI.Computability.PerfectCompleteness.Machines.CircuitLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerBootstrapLemmas
import OAI.Computability.UniqueGames.Machines.MachineLemmas

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.WitnessEncoding

open scoped BigOperators

abbrev Bits (q : Nat) := Fin (2 * q + 1) → Bool

def selector {q : Nat} (bits : Bits q) (i : Fin (q + 1)) : Bool :=
  bits ⟨i.val, by omega⟩

def payload {q : Nat} (bits : Bits q) (i : Fin q) : Bool :=
  bits ⟨q + 1 + i.val, by omega⟩

def pack {q : Nat} (lengthBits : Fin (q + 1) → Bool)
    (payloadBits : Fin q → Bool) : Bits q := fun i =>
  if h : i.val < q + 1 then lengthBits ⟨i.val, h⟩
  else payloadBits ⟨i.val - (q + 1), by omega⟩

@[simp] theorem selector_pack {q : Nat} (lengthBits : Fin (q + 1) → Bool)
    (payloadBits : Fin q → Bool) (i : Fin (q + 1)) :
    selector (pack lengthBits payloadBits) i = lengthBits i := by
  simp [selector, pack, i.isLt]

@[simp] theorem payload_pack {q : Nat} (lengthBits : Fin (q + 1) → Bool)
    (payloadBits : Fin q → Bool) (i : Fin q) :
    payload (pack lengthBits payloadBits) i = payloadBits i := by
  have outside : ¬q + 1 + i.val < q + 1 := by omega
  simp [payload, pack, outside]

def Valid {q : Nat} (bits : Bits q) : Prop :=
  ∃ length : Fin (q + 1), ∀ i, selector bits i = decide (i = length)

theorem valid_iff_local {q : Nat} (bits : Bits q) :
    Valid bits ↔
      (∃ i, selector bits i = true) ∧
      (∀ i j, selector bits i = true → selector bits j = true → i = j) := by
  constructor
  · rintro ⟨length, h⟩
    refine ⟨⟨length, by simp [h]⟩, ?_⟩
    intro i j hi hj
    have hil : i = length := by simpa [h] using hi
    have hjl : j = length := by simpa [h] using hj
    exact hil.trans hjl.symm
  · rintro ⟨⟨length, hl⟩, hu⟩
    refine ⟨length, fun i => ?_⟩
    by_cases hi : i = length
    · subst i; simp [hl]
    · have hf : selector bits i = false := by
        cases hbi : selector bits i
        · rfl
        · exact False.elim (hi (hu i length hbi hl))
      simp [hi, hf]

def selectedLength {q : Nat} (bits : Bits q) : Nat :=
  ∑ i : Fin (q + 1), if selector bits i then i.val else 0

theorem selectedLength_eq {q : Nat} (bits : Bits q) (length : Fin (q + 1))
    (h : ∀ i, selector bits i = decide (i = length)) :
    selectedLength bits = length.val := by
  simp [selectedLength, h]

def decode {q : Nat} (bits : Bits q) : List Bool :=
  (List.ofFn (payload bits)).take (selectedLength bits)

theorem decode_length_le {q : Nat} (bits : Bits q) : (decode bits).length ≤ q := by
  simp [decode]

theorem decode_length_eq {q : Nat} (bits : Bits q) (length : Fin (q + 1))
    (h : ∀ i, selector bits i = decide (i = length)) :
    (decode bits).length = length.val := by
  simp [decode, selectedLength_eq bits length h, Nat.min_eq_left (by omega : length.val ≤ q)]

def encode (q : Nat) (witness : List Bool) (h : witness.length ≤ q) : Bits q :=
  pack (fun i => decide (i = ⟨witness.length, by omega⟩))
    (fun i => witness[i.val]?.getD false)

@[simp] theorem selector_encode (q : Nat) (witness : List Bool)
    (h : witness.length ≤ q) (i : Fin (q + 1)) :
    selector (encode q witness h) i =
      decide (i = ⟨witness.length, by omega⟩) := by
  simp [encode]

@[simp] theorem payload_encode (q : Nat) (witness : List Bool)
    (h : witness.length ≤ q) (i : Fin q) :
    payload (encode q witness h) i = witness[i.val]?.getD false := by
  simp [encode]

theorem encode_valid (q : Nat) (witness : List Bool) (h : witness.length ≤ q) :
    Valid (encode q witness h) :=
  ⟨⟨witness.length, by omega⟩, selector_encode q witness h⟩

@[simp] theorem selectedLength_encode (q : Nat) (witness : List Bool)
    (h : witness.length ≤ q) : selectedLength (encode q witness h) = witness.length :=
  selectedLength_eq _ ⟨witness.length, by omega⟩ (selector_encode q witness h)

@[simp] theorem decode_encode (q : Nat) (witness : List Bool) (h : witness.length ≤ q) :
    decode (encode q witness h) = witness := by
  unfold decode
  rw [selectedLength_encode]
  apply List.ext_getElem?
  intro n
  by_cases hn : n < witness.length
  · have hnq : n < q := Nat.lt_of_lt_of_le hn h
    simp [hn, hnq]
  · simp [hn]

theorem exists_valid_iff (q : Nat) (P : List Bool → Prop) :
    (∃ bits : Bits q, Valid bits ∧ P (decode bits)) ↔
      ∃ witness : List Bool, witness.length ≤ q ∧ P witness := by
  constructor
  · rintro ⟨bits, _, hp⟩
    exact ⟨decode bits, decode_length_le bits, hp⟩
  · rintro ⟨witness, h, hp⟩
    exact ⟨encode q witness h, encode_valid q witness h, by simpa using hp⟩

def present {q : Nat} (bits : Bits q) (n : Nat) : Bool :=
  decide (∃ length : Fin (q + 1), selector bits length = true ∧ n < length.val)

theorem present_eq {q : Nat} (bits : Bits q) (length : Fin (q + 1))
    (h : ∀ i, selector bits i = decide (i = length)) (n : Nat) :
    present bits n = decide (n < length.val) := by
  simp [present, h]

def witnessCell {q : Nat} (bits : Bits q) (n : Nat) : Option Bool :=
  if h : n < q then
    if present bits n then some (payload bits ⟨n, h⟩) else none
  else none

theorem witnessCell_eq_getElem? {q : Nat} (bits : Bits q) (hv : Valid bits) (n : Nat) :
    witnessCell bits n = (decode bits)[n]? := by
  obtain ⟨length, h⟩ := hv
  simp only [witnessCell, decode, selectedLength_eq bits length h,
    present_eq bits length h, List.getElem?_take, List.getElem?_ofFn]
  by_cases hnq : n < q <;> by_cases hnl : n < length.val <;> simp [hnq, hnl]

theorem witnessCell_end {q : Nat} (bits : Bits q) (hv : Valid bits)
    (n : Nat) (hn : (decode bits).length ≤ n) : witnessCell bits n = none := by
  rw [witnessCell_eq_getElem? bits hv, List.getElem?_eq_none hn]

def inputPrefix (input : List Bool) : List Bool := encodeWord input.length ++ input

@[simp] theorem inputPrefix_length (input : List Bool) :
    (inputPrefix input).length = 2 * input.length + 1 := by
  simp only [inputPrefix, List.length_append, encodeWord_length]
  omega

def pairCell {q : Nat} (input : List Bool) (bits : Bits q) (n : Nat) : Option Bool :=
  if n < (inputPrefix input).length then (inputPrefix input)[n]?
  else witnessCell bits (n - (inputPrefix input).length)

theorem pairCell_eq_getElem? {q : Nat} (input : List Bool) (bits : Bits q)
    (hv : Valid bits) (n : Nat) :
    pairCell input bits n = (pairBits (input, decode bits))[n]? := by
  rw [pairBits]
  change pairCell input bits n = (inputPrefix input ++ decode bits)[n]?
  rw [List.getElem?_append]
  simp only [pairCell, witnessCell_eq_getElem? bits hv]

theorem pairBits_decode_length_le {q : Nat} (input : List Bool) (bits : Bits q) :
    (pairBits (input, decode bits)).length ≤ 2 * input.length + q + 1 := by
  rw [pairBits_length]
  change 2 * input.length + (decode bits).length + 1 ≤ 2 * input.length + q + 1
  have h := decode_length_le bits
  omega

theorem pairCells_eq_stackEncoding {q : Nat} (input : List Bool) (bits : Bits q)
    (hv : Valid bits) (capacity : Nat) :
    (fun i : Fin capacity => pairCell input bits i.val) =
      StackEncoding.encode capacity (pairBits (input, decode bits)) := by
  funext i
  exact pairCell_eq_getElem? input bits hv i.val

noncomputable def freeInputPolynomial (q : Polynomial Nat) : Polynomial Nat := 2 * q + 1

@[simp] theorem freeInputPolynomial_eval (q : Polynomial Nat) (n : Nat) :
    (freeInputPolynomial q).eval n = 2 * q.eval n + 1 := by
  simp [freeInputPolynomial]

def localConstraintSites (q : Nat) : Nat := (q + 1) + (q + 1) ^ 2 + q * (q + 1)

theorem localConstraintSites_le (q : Nat) : localConstraintSites q ≤ 3 * (q + 1) ^ 2 := by
  unfold localConstraintSites
  nlinarith

noncomputable def localConstraintPolynomial (q : Polynomial Nat) : Polynomial Nat := 3 * (q + 1) ^ 2

theorem localConstraintSites_le_eval (q : Polynomial Nat) (n : Nat) :
    localConstraintSites (q.eval n) ≤ (localConstraintPolynomial q).eval n := by
  simpa [localConstraintPolynomial] using localConstraintSites_le (q.eval n)


variable (verifier : NPVerifier) (input : List Bool)

def initial (bits : Bits (verifier.witnessBound.eval input.length)) :
    verifier.computation.tm.Cfg :=
  Turing.initList verifier.computation.tm
    ((pairBits (input, decode bits)).map verifier.computation.inputAlphabet.invFun)

@[simp] theorem initial_control (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).l = some verifier.computation.tm.main := rfl

@[simp] theorem initial_state (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).var = verifier.computation.tm.initialState := rfl

@[simp] theorem initial_input_stack (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).stk verifier.computation.tm.k₀ =
      (pairBits (input, decode bits)).map verifier.computation.inputAlphabet.invFun := by
  simp [initial, Turing.initList]

theorem initial_other_stack (bits : Bits (verifier.witnessBound.eval input.length))
    (k : verifier.computation.tm.K) (hk : k ≠ verifier.computation.tm.k₀) :
    (initial verifier input bits).stk k = [] := by
  simp [initial, Turing.initList, hk]

theorem initial_input_cell (bits : Bits (verifier.witnessBound.eval input.length))
    (hv : Valid bits) (n : Nat) :
    ((initial verifier input bits).stk verifier.computation.tm.k₀)[n]? =
      (pairCell input bits n).map verifier.computation.inputAlphabet.invFun := by
  rw [initial_input_stack, List.getElem?_map, pairCell_eq_getElem? input bits hv]

theorem initial_input_end (bits : Bits (verifier.witnessBound.eval input.length))
    (n : Nat) (hn : 2 * input.length + (decode bits).length + 1 ≤ n) :
    ((initial verifier input bits).stk verifier.computation.tm.k₀)[n]? = none := by
  rw [initial_input_stack]
  apply List.getElem?_eq_none
  simpa only [List.length_map, pairBits_length] using hn

theorem initial_stack_length_le (bits : Bits (verifier.witnessBound.eval input.length))
    (k : verifier.computation.tm.K) :
    ((initial verifier input bits).stk k).length ≤
      2 * input.length + verifier.witnessBound.eval input.length + 1 := by
  by_cases hk : k = verifier.computation.tm.k₀
  · subst k
    rw [initial_input_stack, List.length_map]
    exact pairBits_decode_length_le input bits
  · rw [initial_other_stack verifier input bits k hk]
    simp

theorem initial_encode (witness : List Bool)
    (h : witness.length ≤ verifier.witnessBound.eval input.length) :
    initial verifier input (encode _ witness h) =
      Turing.initList verifier.computation.tm
        ((pairBits (input, witness)).map verifier.computation.inputAlphabet.invFun) := by
  simp [initial]

theorem accepts_iff_valid_assignment :
    verifier.Accepts input ↔
      ∃ bits : Bits (verifier.witnessBound.eval input.length),
        Valid bits ∧ verifier.verify (input, decode bits) = true := by
  exact (exists_valid_iff _ (fun witness => verifier.verify (input, witness) = true)).symm


end UniqueGamesTheorem.Foundations.Complexity.CookLevin.WitnessEncoding


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.VerifierBounds

open Polynomial

def initializationPolynomial (q : Polynomial ℕ) : Polynomial ℕ :=
  C 8 * (q + 1) + C 15

def validationPolynomial (q : Polynomial ℕ) : Polynomial ℕ :=
  C 12 * (q + 1) ^ 2

@[simp] theorem initializationPolynomial_eval (q : Polynomial ℕ) (n : ℕ) :
    (initializationPolynomial q).eval n = 8 * (q.eval n + 1) + 15 := by
  simp [initializationPolynomial]

@[simp] theorem validationPolynomial_eval (q : Polynomial ℕ) (n : ℕ) :
    (validationPolynomial q).eval n = 12 * (q.eval n + 1) ^ 2 := by
  simp [validationPolynomial]

def gatesPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ)
    (initialization validation : Polynomial ℕ) : Polynomial ℕ :=
  let W := Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits
  W * initialization + validation +
    Bounds.horizonPolynomial p q * ((W + 1) * C expressionCost) +
    (C 3 * W + C 4)

@[simp] theorem gatesPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ)
    (initialization validation : Polynomial ℕ) (n : ℕ) :
    (gatesPolynomial p q pushes controlBits alphabetBits expressionCost initialization validation).eval n =
      (Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n *
          initialization.eval n + validation.eval n +
        (Bounds.horizonPolynomial p q).eval n *
          (((Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n + 1) *
            expressionCost) +
        (3 * (Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n + 4) := by
  simp [gatesPolynomial]

def bitsPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ)
    (initialization validation : Polynomial ℕ) : Polynomial ℕ :=
  Bounds.circuitBitsPolynomial (WitnessEncoding.freeInputPolynomial q)
    (gatesPolynomial p q pushes controlBits alphabetBits expressionCost initialization validation)

def machineGatesPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ) : Polynomial ℕ :=
  gatesPolynomial p q pushes controlBits alphabetBits expressionCost
    (initializationPolynomial q) (validationPolynomial q)

def machineBitsPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ) : Polynomial ℕ :=
  bitsPolynomial p q pushes controlBits alphabetBits expressionCost
    (initializationPolynomial q) (validationPolynomial q)

@[simp] theorem machineGatesPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost n : ℕ) :
    (machineGatesPolynomial p q pushes controlBits alphabetBits expressionCost).eval n =
      (Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n *
          (8 * (q.eval n + 1) + 15) + 12 * (q.eval n + 1) ^ 2 +
        (Bounds.horizonPolynomial p q).eval n *
          (((Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n + 1) *
            expressionCost) +
        (3 * (Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n + 4) := by
  simp only [machineGatesPolynomial, gatesPolynomial_eval,
    initializationPolynomial_eval, validationPolynomial_eval]

theorem toFormula_bits_le (circuit : Circuit) (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ)
    (initialization validation : Polynomial ℕ) (n : ℕ)
    (hi : circuit.inputs ≤ 2 * q.eval n + 1)
    (hg : circuit.gates.length ≤
      (Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n *
          initialization.eval n + validation.eval n +
        (Bounds.horizonPolynomial p q).eval n *
          (((Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n + 1) *
            expressionCost) +
        (3 * (Bounds.configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n + 4)) :
    (formulaBits circuit.toFormula).length ≤
      (bitsPolynomial p q pushes controlBits alphabetBits expressionCost initialization validation).eval n := by
  apply Bounds.toFormula_bits_length_le_polynomial
  · simpa only [WitnessEncoding.freeInputPolynomial_eval] using hi
  · simpa only [gatesPolynomial_eval] using hg

theorem toFormula_bits_le_machinePolynomial (circuit : Circuit) (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost n : ℕ)
    (hi : circuit.inputs ≤ 2 * q.eval n + 1)
    (hg : circuit.gates.length ≤
      (machineGatesPolynomial p q pushes controlBits alphabetBits expressionCost).eval n) :
    (formulaBits circuit.toFormula).length ≤
      (machineBitsPolynomial p q pushes controlBits alphabetBits expressionCost).eval n := by
  apply Bounds.toFormula_bits_length_le_polynomial
  · simpa only [WitnessEncoding.freeInputPolynomial_eval] using hi
  · exact hg

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.VerifierBounds

end

end OAI
