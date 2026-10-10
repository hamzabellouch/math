import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.CookLevin.Bounds
import OAI.Computability.BinPacking.CookLevin.OutputOrder

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin

def decodePairAux : Nat → List Bool → Option (List Bool × List Bool)
  | _, [] => none
  | read, true :: rest => decodePairAux (read + 1) rest
  | read, false :: rest =>
      if read ≤ rest.length then some (rest.take read, rest.drop read) else none

def decodePair (bits : List Bool) : Option (List Bool × List Bool) :=
  decodePairAux 0 bits

theorem decodePairAux_frame (read count : Nat) (rest : List Bool) :
    decodePairAux read (List.replicate count true ++ false :: rest) =
      if read + count ≤ rest.length then
        some (rest.take (read + count), rest.drop (read + count)) else none := by
  induction count generalizing read with
  | zero => simp [decodePairAux]
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, decodePairAux, ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 count]

@[simp] theorem decodePair_pairBits (input : List Bool × List Bool) :
    decodePair (pairBits input) = some input := by
  rcases input with ⟨x, witness⟩
  simp [decodePair, pairBits, encodeWord, List.append_assoc,
    decodePairAux_frame]

theorem pairBits_injective : Function.Injective pairBits := by
  intro first second same
  have h := congrArg decodePair same
  simpa only [decodePair_pairBits, Option.some.injEq] using h

@[simp] theorem pairBits_length (input : List Bool × List Bool) :
    (pairBits input).length = 2 * input.1.length + input.2.length + 1 := by
  simp only [pairBits, List.length_append, encodeWord_length]
  omega

def pairEncoding : Computability.Encoding (List Bool × List Bool) Bool where
  encode := pairBits
  decode := decodePair
  decode_encode := decodePair_pairBits

theorem NPVerifier.acceptedLanguage_inNP (verifier : NPVerifier) :
    InNP verifier.Accepts := ⟨verifier, fun _ => Iff.rfl⟩

structure PolynomialThreeSATReduction (language : List Bool → Prop) where
  reduce : List Bool → Target.Formula
  computation : Turing.TM2ComputableInPolyTime id formulaBits reduce
  correct : ∀ input, language input ↔ (reduce input).Satisfiable

noncomputable def NPVerifier.horizon (verifier : NPVerifier) (inputLength : Nat) : Nat :=
  verifier.computation.time.eval
    (2 * inputLength + verifier.witnessBound.eval inputLength + 1)

theorem NPVerifier.input_time_le_horizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    verifier.computation.time.eval (pairBits (input, witness)).length ≤
      verifier.horizon input.length := by
  apply MachineComposition.natPolynomial_eval_mono
  rw [pairBits_length]
  exact Nat.add_le_add_right (Nat.add_le_add_left bounded _) _

def NPVerifier.runWithinHorizon (verifier : NPVerifier)
    (input witness : List Bool)
    (bounded : witness.length ≤ verifier.witnessBound.eval input.length) :
    Turing.TM2OutputsInTime verifier.computation.tm
      ((pairBits (input, witness)).map verifier.computation.inputAlphabet.invFun)
      (some ([verifier.verify (input, witness)].map verifier.computation.outputAlphabet.invFun))
      (verifier.horizon input.length) where
  toEvalsTo := (verifier.computation.outputsFun (input, witness)).toEvalsTo
  steps_le_m := Nat.le_trans
    (verifier.computation.outputsFun (input, witness)).steps_le_m
    (verifier.input_time_le_horizon input witness bounded)

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

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
  simp [payload, pack]
  omega

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

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

open StatementCircuit WitnessEncoding

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem eval_disjoin_ofFn_true {ι : Type*} {n : Nat}
    (input : ι → Bool) (es : Fin n → Expr ι) :
    (Expr.disjoin (List.ofFn es)).eval input = true ↔ ∃ i, (es i).eval input = true := by
  rw [Expr.eval_disjoin_true]
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨es i, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩

def selectorExpr (q : Nat) (i : Fin (q + 1)) : Expr (Fin (2 * q + 1)) :=
  .input ⟨i.val, by omega⟩

def payloadExpr (q : Nat) (i : Fin q) : Expr (Fin (2 * q + 1)) :=
  .input ⟨q + 1 + i.val, by omega⟩

@[simp] theorem eval_selectorExpr {q : Nat} (bits : Bits q) (i : Fin (q + 1)) :
    (selectorExpr q i).eval bits = selector bits i := rfl

@[simp] theorem eval_payloadExpr {q : Nat} (bits : Bits q) (i : Fin q) :
    (payloadExpr q i).eval bits = payload bits i := rfl

def nonemptyExpr (q : Nat) : Expr (Fin (2 * q + 1)) :=
  .disjoin (List.ofFn (selectorExpr q))

def clashPairExpr (q : Nat) (i j : Fin (q + 1)) : Expr (Fin (2 * q + 1)) :=
  if i = j then .const false else .and (selectorExpr q i) (selectorExpr q j)

def clashExpr (q : Nat) : Expr (Fin (2 * q + 1)) :=
  .disjoin (List.ofFn fun i => .disjoin (List.ofFn (clashPairExpr q i)))

def validityExpr (q : Nat) : Expr (Fin (2 * q + 1)) :=
  .and (nonemptyExpr q) (.not (clashExpr q))

theorem eval_nonemptyExpr {q : Nat} (bits : Bits q) :
    (nonemptyExpr q).eval bits = true ↔ ∃ i, selector bits i = true := by
  simp only [nonemptyExpr, eval_disjoin_ofFn_true, eval_selectorExpr]

theorem eval_clashPairExpr {q : Nat} (bits : Bits q) (i j : Fin (q + 1)) :
    (clashPairExpr q i j).eval bits = true ↔
      i ≠ j ∧ selector bits i = true ∧ selector bits j = true := by
  by_cases h : i = j <;> simp [clashPairExpr, h, Expr.eval]

theorem eval_clashExpr {q : Nat} (bits : Bits q) :
    (clashExpr q).eval bits = true ↔
      ∃ i j, i ≠ j ∧ selector bits i = true ∧ selector bits j = true := by
  simp only [clashExpr, eval_disjoin_ofFn_true, eval_clashPairExpr]

theorem eval_validityExpr {q : Nat} (bits : Bits q) :
    (validityExpr q).eval bits = true ↔ Valid bits := by
  rw [valid_iff_local]
  simp only [validityExpr, Expr.eval, Bool.and_eq_true, Bool.not_eq_true']
  rw [eval_nonemptyExpr]
  have hc := eval_clashExpr bits
  constructor
  · rintro ⟨hne, hclash⟩
    refine ⟨hne, fun i j hi hj => ?_⟩
    by_contra hij
    have ht := hc.mpr ⟨i, j, hij, hi, hj⟩
    simp [hclash] at ht
  · rintro ⟨hne, hu⟩
    refine ⟨hne, ?_⟩
    cases hb : (clashExpr q).eval bits
    · rfl
    · obtain ⟨i, j, hij, hi, hj⟩ := hc.mp hb
      exact False.elim (hij (hu i j hi hj))

def presenceExpr (q n : Nat) : Expr (Fin (2 * q + 1)) :=
  .disjoin (List.ofFn fun length : Fin (q + 1) =>
    .and (selectorExpr q length) (.const (decide (n < length.val))))

theorem eval_presenceExpr {q : Nat} (bits : Bits q) (n : Nat) :
    (presenceExpr q n).eval bits = present bits n := by
  apply bool_ext
  simp only [presenceExpr, eval_disjoin_ofFn_true, Expr.eval, eval_selectorExpr,
    Bool.and_eq_true, present, decide_eq_true_eq]

section Symbols

variable {A : Type*} [DecidableEq A]

def payloadSymbolExpr (q : Nat) (f : Bool → A) (i : Fin q) (a : Option A) :
    Expr (Fin (2 * q + 1)) :=
  .mux (payloadExpr q i)
    (.const (decide (some (f true) = a))) (.const (decide (some (f false) = a)))

theorem eval_payloadSymbolExpr {q : Nat} (bits : Bits q) (f : Bool → A)
    (i : Fin q) (a : Option A) :
    (payloadSymbolExpr q f i a).eval bits = decide (some (f (payload bits i)) = a) := by
  rw [payloadSymbolExpr, Expr.eval_mux, eval_payloadExpr]
  cases payload bits i <;> simp [Expr.eval]

def inputCellExpr (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    Expr (Fin (2 * q + 1)) :=
  if n < (inputPrefix input).length then
    .const (decide (((inputPrefix input)[n]?).map f = a))
  else if h : n - (inputPrefix input).length < q then
    .mux (presenceExpr q (n - (inputPrefix input).length))
      (payloadSymbolExpr q f ⟨n - (inputPrefix input).length, h⟩ a)
      (.const (decide ((none : Option A) = a)))
  else .const (decide ((none : Option A) = a))

theorem eval_inputCellExpr {q : Nat} (bits : Bits q) (input : List Bool)
    (f : Bool → A) (n : Nat) (a : Option A) :
    (inputCellExpr q input f n a).eval bits = decide ((pairCell input bits n).map f = a) := by
  by_cases hp : n < (inputPrefix input).length
  · simp only [inputCellExpr, pairCell, ite_eq_left hp, Expr.eval]
  · by_cases hq : n - (inputPrefix input).length < q
    · simp only [inputCellExpr, hp, ite_false, hq, dite_eq_left, Expr.eval_mux,
        eval_presenceExpr, eval_payloadSymbolExpr, Expr.eval, pairCell, witnessCell]
      cases present bits (n - (inputPrefix input).length) <;> simp
    · simp only [inputCellExpr, pairCell, witnessCell, ite_eq_right hp, dite_eq_right hq,
        Expr.eval, Option.map_none]

end Symbols

section Size

@[simp] theorem size_selectorExpr (q : Nat) (i : Fin (q + 1)) :
    (selectorExpr q i).size = 1 := rfl

@[simp] theorem size_payloadExpr (q : Nat) (i : Fin q) :
    (payloadExpr q i).size = 1 := rfl

theorem size_mux {ι : Type*} (c y n : Expr ι) :
    (Expr.mux c y n).size = 2 * c.size + y.size + n.size + 4 := by
  simp only [Expr.mux, Expr.size]
  omega

theorem size_nonemptyExpr_le (q : Nat) :
    (nonemptyExpr q).size ≤ 2 * (q + 1) + 1 := by
  have h := Expr.size_disjoin_le (List.ofFn (selectorExpr q)) 1 (by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    simp)
  simpa [nonemptyExpr, Nat.mul_comm] using h

theorem size_clashPairExpr_le (q : Nat) (i j : Fin (q + 1)) :
    (clashPairExpr q i j).size ≤ 3 := by
  by_cases h : i = j <;> simp [clashPairExpr, h, Expr.size, selectorExpr]

theorem size_clashExpr_le (q : Nat) :
    (clashExpr q).size ≤ (q + 1) * (4 * (q + 1) + 2) + 1 := by
  have hi (i : Fin (q + 1)) :
      (Expr.disjoin (List.ofFn (clashPairExpr q i))).size ≤ 4 * (q + 1) + 1 := by
    have h := Expr.size_disjoin_le (List.ofFn (clashPairExpr q i)) 3 (by
      intro e he
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
      exact size_clashPairExpr_le q i j)
    simpa [Nat.mul_comm] using h
  have h := Expr.size_disjoin_le
    (List.ofFn fun i => Expr.disjoin (List.ofFn (clashPairExpr q i)))
    (4 * (q + 1) + 1) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact hi i)
  simpa [clashExpr, Nat.add_assoc] using h

theorem size_validityExpr_le (q : Nat) : (validityExpr q).size ≤ 12 * (q + 1) ^ 2 := by
  have hn := size_nonemptyExpr_le q
  have hc := size_clashExpr_le q
  simp only [validityExpr, Expr.size]
  nlinarith

theorem size_presenceExpr_le (q n : Nat) : (presenceExpr q n).size ≤ 4 * (q + 1) + 1 := by
  have h := Expr.size_disjoin_le
    (List.ofFn fun length : Fin (q + 1) =>
      Expr.and (selectorExpr q length) (.const (decide (n < length.val)))) 3 (by
        intro e he
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
        simp [Expr.size])
  simpa [presenceExpr, Nat.mul_comm] using h

theorem size_payloadSymbolExpr {A : Type*} [DecidableEq A]
    (q : Nat) (f : Bool → A) (i : Fin q) (a : Option A) :
    (payloadSymbolExpr q f i a).size = 8 := by
  simp [payloadSymbolExpr, size_mux, Expr.size]

theorem size_inputCellExpr_le {A : Type*} [DecidableEq A]
    (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    (inputCellExpr q input f n a).size ≤ 8 * (q + 1) + 15 := by
  unfold inputCellExpr
  split
  · simp [Expr.size]
  · split
    · rw [size_mux, size_payloadSymbolExpr]
      have h := size_presenceExpr_le q (n - (inputPrefix input).length)
      simp only [Expr.size]
      omega
    · simp [Expr.size]

end Size

section Initial

variable (verifier : NPVerifier)
variable [DecidableEq verifier.computation.tm.Λ]
variable [DecidableEq verifier.computation.tm.σ]
variable [∀ k, DecidableEq (verifier.computation.tm.Γ k)]

def initialCellExpr (input : List Bool) (S : Nat)
    (k : verifier.computation.tm.K) (i : Fin S) (a : Option (verifier.computation.tm.Γ k)) :
    Expr (Fin (2 * verifier.witnessBound.eval input.length + 1)) :=
  if h : k = verifier.computation.tm.k₀ then by
    subst k
    exact inputCellExpr _ input verifier.computation.inputAlphabet.invFun i.val a
  else .const (decide ((none : Option (verifier.computation.tm.Γ k)) = a))

omit [DecidableEq verifier.computation.tm.Λ] [DecidableEq verifier.computation.tm.σ] in
theorem eval_initialCellExpr (input : List Bool) (S : Nat)
    (bits : Bits (verifier.witnessBound.eval input.length)) (hv : Valid bits)
    (k : verifier.computation.tm.K) (i : Fin S) (a : Option (verifier.computation.tm.Γ k)) :
    (initialCellExpr verifier input S k i a).eval bits =
      decide (StackEncoding.encode S ((initial verifier input bits).stk k) i = a) := by
  by_cases hk : k = verifier.computation.tm.k₀
  · subst k
    simpa [initialCellExpr, StackEncoding.encode,
      pairCell_eq_getElem? input bits hv i.val] using
        eval_inputCellExpr bits input verifier.computation.inputAlphabet.invFun i.val a
  · simp [initialCellExpr, hk, initial_other_stack verifier input bits k hk,
      StackEncoding.encode, Expr.eval]

def initExpr (input : List Bool) (S : Nat) :
    ConfigBit verifier.computation.tm.Γ verifier.computation.tm.Λ verifier.computation.tm.σ S →
      Expr (Fin (2 * verifier.witnessBound.eval input.length + 1))
  | .inl label => .const (decide (some verifier.computation.tm.main = label))
  | .inr (.inl state) => .const (decide (verifier.computation.tm.initialState = state))
  | .inr (.inr ⟨k, i, a⟩) => initialCellExpr verifier input S k i a

theorem eval_initExpr (input : List Bool) (S : Nat)
    (bits : Bits (verifier.witnessBound.eval input.length)) (hv : Valid bits)
    (bit : ConfigBit verifier.computation.tm.Γ verifier.computation.tm.Λ
      verifier.computation.tm.σ S) :
    (initExpr verifier input S bit).eval bits =
      configEncoding S (initial verifier input bits) bit := by
  rcases bit with label | (state | ⟨k, i, a⟩)
  · rfl
  · rfl
  · exact eval_initialCellExpr verifier input S bits hv k i a

omit [DecidableEq verifier.computation.tm.Λ] [DecidableEq verifier.computation.tm.σ] in
theorem size_initialCellExpr_le (input : List Bool) (S : Nat)
    (k : verifier.computation.tm.K) (i : Fin S) (a : Option (verifier.computation.tm.Γ k)) :
    (initialCellExpr verifier input S k i a).size ≤
      8 * (verifier.witnessBound.eval input.length + 1) + 15 := by
  by_cases hk : k = verifier.computation.tm.k₀
  · subst k
    simpa [initialCellExpr] using
      size_inputCellExpr_le (verifier.witnessBound.eval input.length) input
        verifier.computation.inputAlphabet.invFun i.val a
  · simp [initialCellExpr, hk, Expr.size]

theorem size_initExpr_le (input : List Bool) (S : Nat)
    (bit : ConfigBit verifier.computation.tm.Γ verifier.computation.tm.Λ
      verifier.computation.tm.σ S) :
    (initExpr verifier input S bit).size ≤
      8 * (verifier.witnessBound.eval input.length + 1) + 15 := by
  rcases bit with label | (state | ⟨k, i, a⟩)
  · simp [initExpr, Expr.size]
  · simp [initExpr, Expr.size]
  · exact size_initialCellExpr_le verifier input S k i a

end Initial

def validityCircuit (q : Nat) : Circuit := (validityExpr q).circuit id

theorem validityCircuit_eval {q : Nat} (bits : Bits q) :
    (validityCircuit q).eval bits = true ↔ Valid bits := by
  change ((validityExpr q).circuit id).eval bits = true ↔ Valid bits
  rw [Expr.circuit_eval]
  exact eval_validityExpr bits

theorem validityCircuit_gates_le (q : Nat) :
    (validityCircuit q).gates.length ≤ 12 * (q + 1) ^ 2 := by
  simpa only [validityCircuit, Expr.circuit, Expr.gates_length] using size_validityExpr_le q

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierBounds

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

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierBounds

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

local instance alphabetFinite (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) :=
  V.finiteAlphabet
local instance labelFinite (V : NPVerifier) : Fintype V.computation.tm.Λ :=
  V.computation.tm.ΛFin
local instance stateFinite (V : NPVerifier) : Fintype V.computation.tm.σ :=
  V.computation.tm.σFin
local instance labelDecidable (V : NPVerifier) : DecidableEq V.computation.tm.Λ :=
  Classical.decEq _
local instance stateDecidable (V : NPVerifier) : DecidableEq V.computation.tm.σ :=
  Classical.decEq _
local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def capacity (V : NPVerifier) (n : Nat) : Nat :=
  2 * n + V.witnessBound.eval n + 1 + V.horizon n * Runtime.programPushBound V.computation.tm

theorem capacity_pos (V : NPVerifier) (n : Nat) : 1 ≤ capacity V n := by
  unfold capacity
  omega

abbrev FreeBits (V : NPVerifier) (input : List Bool) :=
  WitnessEncoding.Bits (V.witnessBound.eval input.length)

def machineInput (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :=
  (pairBits (input, WitnessEncoding.decode bits)).map V.computation.inputAlphabet.invFun

def actualRun (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) (t : Nat) :
    V.computation.tm.Cfg := BoundedExecution.run V.computation.tm (machineInput V input bits) t

def accepting (V : NPVerifier) : V.computation.tm.Cfg :=
  haltList V.computation.tm ([true].map V.computation.outputAlphabet.invFun)

theorem stackCapacity_le (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    BoundedExecution.stackCapacity V.computation.tm (machineInput V input bits)
      (V.horizon input.length) ≤ capacity V input.length := by
  have h := WitnessEncoding.pairBits_decode_length_le input bits
  simp only [BoundedExecution.stackCapacity, machineInput, List.length_map, capacity]
  omega

theorem actualRun_stack_le (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) (ht : t ≤ V.horizon input.length) (k : V.computation.tm.K) :
    ((actualRun V input bits t).stk k).length ≤ capacity V input.length :=
  (BoundedExecution.run_stack_le V.computation.tm (machineInput V input bits)
    (V.horizon input.length) t ht k).trans (stackCapacity_le V input bits)

theorem actualRun_stepSafe (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) (ht : t < V.horizon input.length) :
    MachineCircuit.StepSafe (capacity V input.length) V.computation.tm.m
      (actualRun V input bits t) := by
  intro label _
  apply BoundedExecution.statementSafe_of_budget
  intro k
  exact (BoundedExecution.statement_budget V.computation.tm (machineInput V input bits)
    (V.horizon input.length) t ht label k).trans (stackCapacity_le V input bits)

theorem accepting_stack_le (V : NPVerifier) (input : List Bool) (k : V.computation.tm.K) :
    ((accepting V).stk k).length ≤ capacity V input.length := by
  by_cases hk : k = V.computation.tm.k₁
  · subst k
    simpa [accepting, haltList] using capacity_pos V input.length
  · simp [accepting, haltList, hk]

theorem actualRun_accepting_iff (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    actualRun V input bits (V.horizon input.length) = accepting V ↔
      V.verify (input, WitnessEncoding.decode bits) = true := by
  have hr := BoundedExecution.run_eq_halt_of_outputs V.computation.tm
    (machineInput V input bits)
    ([V.verify (input, WitnessEncoding.decode bits)].map V.computation.outputAlphabet.invFun)
    (V.horizon input.length)
    (V.runWithinHorizon input (WitnessEncoding.decode bits) (WitnessEncoding.decode_length_le bits))
  change actualRun V input bits (V.horizon input.length) = _ at hr
  rw [hr]
  constructor
  · intro h
    have hs := congrArg (fun c : V.computation.tm.Cfg => c.stk V.computation.tm.k₁) h
    have he : V.computation.outputAlphabet.invFun (V.verify (input, WitnessEncoding.decode bits)) =
        V.computation.outputAlphabet.invFun true := by
      simpa [accepting, haltList] using hs
    exact V.computation.outputAlphabet.symm.injective he
  · intro h
    simp [h, accepting]

abbrev Bit (V : NPVerifier) (input : List Bool) :=
  ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ (capacity V input.length)

def indexing (V : NPVerifier) :
    ConfigIndex.Indexing V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ :=
  ConfigIndex.ofMachine V.computation.tm

abbrev width (V : NPVerifier) (input : List Bool) : Nat :=
  (indexing V).width (capacity V input.length)

def bitEquiv (V : NPVerifier) (input : List Bool) : Bit V input ≃ Fin (width V input) :=
  (indexing V).configIndexEquiv (capacity V input.length)

def bitWire (V : NPVerifier) (input : List Bool) (b : Bit V input) : Fin (width V input + 1) :=
  (bitEquiv V input b).castSucc

def stateEncoding (V : NPVerifier) (input : List Bool) (cfg : V.computation.tm.Cfg)
    (valid : Bool) : Fin (width V input + 1) → Bool :=
  Fin.lastCases valid (fun j => configEncoding (capacity V input.length) cfg
    ((bitEquiv V input).symm j))

@[simp] theorem stateEncoding_last (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool) :
    stateEncoding V input cfg valid (Fin.last (width V input)) = valid := by
  simp [stateEncoding]

@[simp] theorem stateEncoding_bitWire (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool) (b : Bit V input) :
    stateEncoding V input cfg valid (bitWire V input b) =
      configEncoding (capacity V input.length) cfg b := by
  simp [stateEncoding, bitWire]

def initialExpressions (V : NPVerifier) (input : List Bool) :
    Fin (width V input + 1) → Expr (Fin (2 * V.witnessBound.eval input.length + 1)) :=
  Fin.lastCases (WitnessCircuit.validityExpr (V.witnessBound.eval input.length))
    (fun j => WitnessCircuit.initExpr V input (capacity V input.length)
      ((bitEquiv V input).symm j))

def stepExpressions (V : NPVerifier) (input : List Bool) :
    Fin (width V input + 1) → Expr (Fin (width V input + 1)) :=
  Fin.lastCases (.input (Fin.last (width V input)))
    (fun j => (MachineCircuit.stickyExpr (capacity V input.length) V.computation.tm.m
      ((bitEquiv V input).symm j)).rename (bitWire V input))

theorem initialExpressions_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) :
    (fun j => (initialExpressions V input j).eval bits) =
      stateEncoding V input (WitnessEncoding.initial V input bits)
        ((WitnessCircuit.validityExpr _).eval bits) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [initialExpressions, stateEncoding]
  · simpa [initialExpressions, stateEncoding] using
      WitnessCircuit.eval_initExpr V input (capacity V input.length) bits hv
        ((bitEquiv V input).symm i)

theorem stepExpressions_eval (V : NPVerifier) (input : List Bool) (cfg : V.computation.tm.Cfg)
    (safe : MachineCircuit.StepSafe (capacity V input.length) V.computation.tm.m cfg)
    (valid : Bool) :
    Frame.network (stepExpressions V input) (stateEncoding V input cfg valid) =
      stateEncoding V input (BoundedExecution.stickyNext V.computation.tm cfg) valid := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Frame.network, stepExpressions, Expr.eval, stateEncoding]
  · simp only [Frame.network, stepExpressions, Fin.lastCases_castSucc, Expr.eval_rename]
    have he : (fun b => stateEncoding V input cfg valid (bitWire V input b)) =
        configEncoding (capacity V input.length) cfg := by funext b; simp
    rw [he, MachineCircuit.stickyExpr_eval _ _ cfg safe]
    simp only [stateEncoding, Fin.lastCases_castSucc]
    rfl

def initialFrame (V : NPVerifier) (input : List Bool) :
    Frame (2 * V.witnessBound.eval input.length + 1) (width V input + 1) :=
  (Frame.initial id).step (initialExpressions V input)

def timeFrame (V : NPVerifier) (input : List Bool) (t : Nat) :
    Frame (2 * V.witnessBound.eval input.length + 1) (width V input + 1) :=
  (initialFrame V input).repeat (stepExpressions V input) t

theorem initialFrame_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) :
    (initialFrame V input).eval bits = stateEncoding V input
      (WitnessEncoding.initial V input bits) ((WitnessCircuit.validityExpr _).eval bits) := by
  rw [initialFrame, Frame.step_eval_fun]
  have hi : (Frame.initial id).eval bits = bits := by funext i; simp
  rw [hi]
  exact initialExpressions_eval V input bits hv

theorem timeFrame_validity (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) :
    (timeFrame V input t).eval bits (Fin.last (width V input)) =
      (WitnessCircuit.validityExpr (V.witnessBound.eval input.length)).eval bits := by
  induction t with
  | zero =>
    simp only [timeFrame, Frame.repeat, initialFrame, Frame.step_eval,
      initialExpressions, Fin.lastCases_last]
    apply Expr.eval_congr
    intro i
    exact Frame.initial_eval id bits i
  | succ t ih =>
    simpa only [timeFrame, Frame.repeat, Frame.step_eval, stepExpressions,
      Fin.lastCases_last, Expr.eval] using ih

theorem timeFrame_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) (t : Nat) (ht : t ≤ V.horizon input.length) :
    (timeFrame V input t).eval bits = stateEncoding V input (actualRun V input bits t)
      ((WitnessCircuit.validityExpr _).eval bits) := by
  induction t with
  | zero => exact initialFrame_eval V input bits hv
  | succ t ih =>
    have hprev := ih (by omega)
    change ((timeFrame V input t).step (stepExpressions V input)).eval bits = _
    rw [Frame.step_eval_fun, hprev]
    have hs := stepExpressions_eval V input (actualRun V input bits t)
      (actualRun_stepSafe V input bits t (by omega))
      ((WitnessCircuit.validityExpr _).eval bits)
    change (fun i => (stepExpressions V input i).eval
      (stateEncoding V input (actualRun V input bits t)
        ((WitnessCircuit.validityExpr _).eval bits))) = _ at hs
    simpa only [actualRun, BoundedExecution.run_succ] using hs

def mismatchExpr (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) :
    Expr (Fin (width V input + 1)) :=
  if configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j)
  then .not (.input j.castSucc) else .input j.castSucc

def acceptanceExpr (V : NPVerifier) (input : List Bool) : Expr (Fin (width V input + 1)) :=
  .and (.input (Fin.last (width V input)))
    (.not (Expr.disjoin (List.ofFn (mismatchExpr V input))))

theorem mismatchExpr_eval (V : NPVerifier) (input : List Bool)
    (state : Fin (width V input + 1) → Bool) (j : Fin (width V input)) :
    (mismatchExpr V input j).eval state = true ↔
      state j.castSucc ≠ configEncoding (capacity V input.length) (accepting V)
        ((bitEquiv V input).symm j) := by
  cases ht : configEncoding (capacity V input.length) (accepting V)
      ((bitEquiv V input).symm j) <;> cases hs : state j.castSucc <;>
    simp [mismatchExpr, Expr.eval, ht, hs]

theorem acceptanceExpr_eval (V : NPVerifier) (input : List Bool)
    (state : Fin (width V input + 1) → Bool) :
    (acceptanceExpr V input).eval state = true ↔
      state (Fin.last (width V input)) = true ∧
      ∀ j : Fin (width V input), state j.castSucc =
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
  have hd : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state = true ↔
      ∃ j : Fin (width V input), state j.castSucc ≠
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
    rw [Expr.eval_disjoin_true]
    constructor
    · rintro ⟨e, he, hv⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
      exact ⟨j, (mismatchExpr_eval V input state j).mp hv⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, (mismatchExpr_eval V input state j).mpr hj⟩
  have hz : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state = false ↔
      ∀ j : Fin (width V input), state j.castSucc =
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
    constructor
    · intro h j
      by_contra hj
      have ht := hd.mpr ⟨j, hj⟩
      rw [h] at ht
      contradiction
    · intro h
      cases ht : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state with
      | false => rfl
      | true =>
        obtain ⟨j, hj⟩ := hd.mp ht
        exact False.elim (hj (h j))
  simp only [acceptanceExpr, Expr.eval, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
  exact and_congr_right (fun _ => hz)

theorem acceptanceExpr_stateEncoding (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool)
    (hcfg : ∀ k, (cfg.stk k).length ≤ capacity V input.length) :
    (acceptanceExpr V input).eval (stateEncoding V input cfg valid) = true ↔
      valid = true ∧ cfg = accepting V := by
  rw [acceptanceExpr_eval]
  constructor
  · rintro ⟨hv, hbits⟩
    refine ⟨by simpa using hv, ?_⟩
    apply MachineCircuit.configEncoding_injective (capacity V input.length)
      cfg (accepting V) hcfg (accepting_stack_le V input)
    funext b
    have h := hbits (bitEquiv V input b)
    simpa [stateEncoding] using h
  · rintro ⟨hv, rfl⟩
    simp [stateEncoding, hv]

def circuitOfVerifier (V : NPVerifier) (input : List Bool) : Circuit :=
  ((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).toCircuit 0

@[simp] theorem circuitOfVerifier_inputs (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).inputs = 2 * V.witnessBound.eval input.length + 1 := rfl

theorem circuitOfVerifier_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    (circuitOfVerifier V input).eval bits =
      (acceptanceExpr V input).eval ((timeFrame V input (V.horizon input.length)).eval bits) := by
  change (((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).toCircuit 0).eval bits = _
  rw [Frame.toCircuit_eval, Frame.step_eval]

theorem circuitOfVerifier_accepts_iff (V : NPVerifier) (input : List Bool)
    (bits : FreeBits V input) :
    (circuitOfVerifier V input).eval bits = true ↔
      WitnessEncoding.Valid bits ∧ V.verify (input, WitnessEncoding.decode bits) = true := by
  rw [circuitOfVerifier_eval]
  constructor
  · intro h
    have hvalid := ((acceptanceExpr_eval V input _).mp h).1
    rw [timeFrame_validity] at hvalid
    have hv : WitnessEncoding.Valid bits := (WitnessCircuit.eval_validityExpr bits).mp hvalid
    rw [timeFrame_eval V input bits hv _ le_rfl] at h
    have he := (acceptanceExpr_stateEncoding V input
      (actualRun V input bits (V.horizon input.length)) _
      (actualRun_stack_le V input bits _ le_rfl)).mp h
    exact ⟨hv, (actualRun_accepting_iff V input bits).mp he.2⟩
  · rintro ⟨hv, hverify⟩
    rw [timeFrame_eval V input bits hv _ le_rfl]
    apply (acceptanceExpr_stateEncoding V input
      (actualRun V input bits (V.horizon input.length)) _
      (actualRun_stack_le V input bits _ le_rfl)).mpr
    exact ⟨(WitnessCircuit.eval_validityExpr bits).mpr hv,
      (actualRun_accepting_iff V input bits).mpr hverify⟩

theorem circuitOfVerifier_correct (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).toFormula.Satisfiable ↔ V.Accepts input := by
  rw [Circuit.toFormula_satisfiable_iff_eval, WitnessEncoding.accepts_iff_valid_assignment]
  change (∃ bits : FreeBits V input, (circuitOfVerifier V input).eval bits = true) ↔ _
  exact exists_congr (fun bits => circuitOfVerifier_accepts_iff V input bits)

theorem mismatchExpr_size_le (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) :
    (mismatchExpr V input j).size ≤ 2 := by
  unfold mismatchExpr
  split <;> simp [Expr.size]

theorem acceptanceExpr_size_le (V : NPVerifier) (input : List Bool) :
    (acceptanceExpr V input).size ≤ 3 * width V input + 4 := by
  have h := Expr.size_disjoin_le (List.ofFn (mismatchExpr V input)) 2 (by
    intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact mismatchExpr_size_le V input j)
  simp only [List.length_ofFn] at h
  simp only [acceptanceExpr, Expr.size]
  omega

theorem stepExpressions_size_le (V : NPVerifier) (input : List Bool)
    (j : Fin (width V input + 1)) :
    (stepExpressions V input j).size ≤ MachineCircuit.expressionCost V.computation.tm.m := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [stepExpressions, Fin.lastCases_last, Expr.size, MachineCircuit.expressionCost]
    omega
  · simpa [stepExpressions] using MachineCircuit.stickyExpr_size_le
      (capacity V input.length) V.computation.tm.m ((bitEquiv V input).symm i)

theorem initialExpressions_cost_le (V : NPVerifier) (input : List Bool) :
    Batch.cost (List.ofFn (initialExpressions V input)) ≤
      width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
      12 * (V.witnessBound.eval input.length + 1) ^ 2 := by
  rw [Batch.cost_ofFn, Fin.sum_univ_castSucc]
  simp only [initialExpressions, Fin.lastCases_castSucc, Fin.lastCases_last]
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _ : Fin (width V input), (8 * (V.witnessBound.eval input.length + 1) + 15) := by
        apply Finset.sum_le_sum
        intro i _
        exact WitnessCircuit.size_initExpr_le V input (capacity V input.length)
          ((bitEquiv V input).symm i)
      _ = _ := by simp
  · exact WitnessCircuit.size_validityExpr_le _

theorem circuitOfVerifier_gate_count (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length =
      Batch.cost (List.ofFn (initialExpressions V input)) +
      V.horizon input.length * Batch.cost (List.ofFn (stepExpressions V input)) +
      (acceptanceExpr V input).size := by
  change ((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).fragment.gates.length = _
  rw [Frame.step_gate_count]
  simp only [timeFrame, Frame.repeat_gate_count, initialFrame, Frame.step_gate_count,
    Frame.initial, Fragment.empty, List.length_nil, Nat.zero_add]
  have hsingle : Batch.cost (List.ofFn (fun _ : Fin 1 => acceptanceExpr V input)) =
      (acceptanceExpr V input).size := by simp [Batch.cost]
  rw [hsingle]

theorem circuitOfVerifier_gates_le (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length ≤
      width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
      12 * (V.witnessBound.eval input.length + 1) ^ 2 +
      V.horizon input.length * ((width V input + 1) *
        MachineCircuit.expressionCost V.computation.tm.m) + (3 * width V input + 4) := by
  rw [circuitOfVerifier_gate_count]
  exact Nat.add_le_add
    (Nat.add_le_add (initialExpressions_cost_le V input)
      (Nat.mul_le_mul_left _ (Batch.cost_ofFn_le _ _ (stepExpressions_size_le V input))))
    (acceptanceExpr_size_le V input)

def widthPolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.configurationWidthPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount

theorem widthPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (widthPolynomial V).eval input.length = width V input := by
  simp [widthPolynomial, width, ConfigIndex.Indexing.width, capacity,
    NPVerifier.horizon, Nat.mul_comm]

def gatePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierBounds.machineGatesPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount
    (MachineCircuit.expressionCost V.computation.tm.m)

def formulaPolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierBounds.machineBitsPolynomial V.computation.time V.witnessBound
    (Runtime.programPushBound V.computation.tm)
    ((indexing V).labelCount + (indexing V).stateCount) (indexing V).symbolCount
    (MachineCircuit.expressionCost V.computation.tm.m)

theorem circuitOfVerifier_gates_le_polynomial (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).gates.length ≤ (gatePolynomial V).eval input.length := by
  have hw := widthPolynomial_eval V input
  unfold widthPolynomial at hw
  simpa only [gatePolynomial, VerifierBounds.machineGatesPolynomial_eval, hw,
    Bounds.horizonPolynomial_eval, NPVerifier.horizon] using
      circuitOfVerifier_gates_le V input

theorem circuitOfVerifier_formulaBits_length_le (V : NPVerifier) (input : List Bool) :
    (formulaBits (circuitOfVerifier V input).toFormula).length ≤
      (formulaPolynomial V).eval input.length := by
  unfold formulaPolynomial
  apply VerifierBounds.toFormula_bits_le_machinePolynomial
  · exact Nat.le_refl _
  · exact circuitOfVerifier_gates_le_polynomial V input

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

end

end OAI
