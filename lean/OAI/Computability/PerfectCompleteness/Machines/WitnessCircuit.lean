import OAI.Computability.PerfectCompleteness.Machines.StatementCircuit
import OAI.Computability.PerfectCompleteness.Machines.WitnessEncodingLemmas

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.WitnessCircuit

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.WitnessCircuit

end OAI
