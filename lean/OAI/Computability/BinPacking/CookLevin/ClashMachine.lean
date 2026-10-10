import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import OAI.Computability.BinPacking.CookLevin.VerifierCircuit

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

section

open PostfixModel

def forTokens : Nat → (Nat → List Token) → List Token
  | 0, _ => []
  | count + 1, body => forTokens count body ++ body count

theorem forTokens_eq_flatMap_range (count : Nat) (body : Nat → List Token) :
    forTokens count body = (List.range count).flatMap body := by
  induction count with
  | zero => rfl
  | succ count ih => simp [forTokens, List.range_succ, ih]

theorem forTokens_eq_ofFn (count : Nat) (body : Nat → List Token) :
    forTokens count body = (List.ofFn fun i : Fin count => body i.val).flatten := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    rw [forTokens, ih, List.ofFn_succ']
    simp [List.concat_eq_append]

theorem forTokens_succ_first (count : Nat) (body : Nat → List Token) :
    forTokens (count + 1) body = body 0 ++ forTokens count (fun j => body (j + 1)) := by
  simp [forTokens_eq_flatMap_range, List.range_succ_eq_map, List.flatMap_map]

theorem forTokens_congr (count : Nat) (first second : Nat → List Token)
    (h : ∀ i, i < count → first i = second i) :
    forTokens count first = forTokens count second := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [forTokens, forTokens, ih (fun i hi => h i (by omega)), h count (by omega)]

theorem forTokens_length_le (count : Nat) (body : Nat → List Token) (cost : Nat)
    (h : ∀ i, i < count → (body i).length ≤ cost) :
    (forTokens count body).length ≤ count * cost := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hl := h count (by omega)
    simp only [forTokens, List.length_append, Nat.succ_mul]
    omega

theorem forTokens_length_eq (count : Nat) (body : Nat → List Token) (cost : Nat)
    (h : ∀ i, i < count → (body i).length = cost) :
    (forTokens count body).length = count * cost := by
  induction count with
  | zero => simp [forTokens]
  | succ count ih =>
    rw [forTokens, List.length_append, ih (fun i hi => h i (by omega)), h count (by omega)]
    exact (Nat.succ_mul count cost).symm

def closeOr (count : Nat) : List Token := [.const false] ++ List.replicate count .or

def nonemptyTokens (q : Nat) : List Token :=
  forTokens (q + 1) (fun i => [.input i]) ++ closeOr (q + 1)

def clashPairTokens (i j : Nat) : List Token :=
  if i = j then [.const false] else [.input i, .input j, .and]

def clashRowTokens (q i : Nat) : List Token :=
  forTokens (q + 1) (clashPairTokens i) ++ closeOr (q + 1)

def clashTokens (q : Nat) : List Token :=
  forTokens (q + 1) (clashRowTokens q) ++ closeOr (q + 1)

def validityTokens (q : Nat) : List Token :=
  nonemptyTokens q ++ clashTokens q ++ [.not, .and]

def presenceTokens (q n : Nat) : List Token :=
  forTokens (q + 1) (fun length => [.input length, .const (decide (n < length)), .and]) ++
    closeOr (q + 1)

def selectorLoopTokens (count start threshold : Nat) : List Token :=
  forTokens count (fun j => [.input (start + j), .const (decide (threshold ≤ j)), .and])

theorem threshold_zero_iff (threshold used : Nat) :
    threshold - used = 0 ↔ threshold ≤ used := Nat.sub_eq_zero_iff_le

theorem selectorLoopTokens_length (count start threshold : Nat) :
    (selectorLoopTokens count start threshold).length = 3 * count := by
  simpa only [selectorLoopTokens, Nat.mul_comm] using
    forTokens_length_eq count
      (fun j => [.input (start + j), .const (decide (threshold ≤ j)), .and]) 3
      (fun _ _ => rfl)

theorem selectorLoopTokens_succ (count start threshold : Nat) :
    selectorLoopTokens (count + 1) start threshold =
      [.input start, .const (decide (threshold = 0)), .and] ++
        selectorLoopTokens count (start + 1) (threshold - 1) := by
  rw [selectorLoopTokens, forTokens_succ_first]
  simp only [Nat.add_zero, Nat.le_zero]
  apply congrArg (List.append [Token.input start, Token.const (decide (threshold = 0)), Token.and])
  apply forTokens_congr
  intro j _
  have ha : start + (j + 1) = start + 1 + j := by omega
  have ht : (threshold ≤ j + 1) = (threshold - 1 ≤ j) := propext (by omega)
  simp only [ha, ht]

theorem selectorLoopTokens_presence (q n : Nat) :
    selectorLoopTokens (q + 1) 0 (n + 1) ++ closeOr (q + 1) = presenceTokens q n := by
  simp only [selectorLoopTokens, presenceTokens]
  apply congrArg (fun xs : List Token => xs ++ closeOr (q + 1))
  apply forTokens_congr
  intro j _
  simp only [Nat.zero_add, Nat.succ_le_iff]

theorem presenceTokens_length (q n : Nat) : (presenceTokens q n).length = 4 * (q + 1) + 1 := by
  rw [← selectorLoopTokens_presence q n, List.length_append, selectorLoopTokens_length]
  simp only [closeOr, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

end

open StatementCircuit WitnessCircuit WitnessEncoding PostfixModel PostfixAlignment CircuitBatch

theorem exprTokens_disjoin {ι : Type*} (wire : ι → Nat) (es : List (Expr ι)) :
    exprTokens wire (Expr.disjoin es) = forestTokens wire es ++ closeOr es.length := by
  induction es with
  | nil => simp [Expr.disjoin, exprTokens, forestTokens, closeOr]
  | cons e es ih =>
    simp [Expr.disjoin, exprTokens, forestTokens_cons, ih, closeOr,
      List.replicate_succ', List.append_assoc]

theorem forestTokens_ofFn {ι : Type*} (wire : ι → Nat) (n : Nat) (es : Fin n → Expr ι) :
    forestTokens wire (List.ofFn es) = (List.ofFn fun i => exprTokens wire (es i)).flatten := by
  simp only [forestTokens, List.flatMap_def, List.map_ofFn, Function.comp_def]

def muxTokens (condition yes no : List Token) : List Token :=
  condition ++ yes ++ [.and] ++ condition ++ [.not] ++ no ++ [.and, .or]

theorem exprTokens_mux {ι : Type*} (wire : ι → Nat) (c y n : Expr ι) :
    exprTokens wire (Expr.mux c y n) =
      muxTokens (exprTokens wire c) (exprTokens wire y) (exprTokens wire n) := by
  simp [Expr.mux, exprTokens, muxTokens, List.append_assoc]

theorem nonemptyTokens_eq (q : Nat) :
    nonemptyTokens q = exprTokens Fin.val (nonemptyExpr q) := by
  rw [nonemptyExpr, exprTokens_disjoin, forestTokens_ofFn]
  simp [nonemptyTokens, forTokens_eq_ofFn, selectorExpr, exprTokens]

theorem clashPairTokens_eq (q : Nat) (i j : Fin (q + 1)) :
    clashPairTokens i.val j.val = exprTokens Fin.val (clashPairExpr q i j) := by
  by_cases h : i = j
  · subst j; simp [clashPairTokens, clashPairExpr, exprTokens]
  · have hv : i.val ≠ j.val := fun hval => h (Fin.ext hval)
    simp [clashPairTokens, clashPairExpr, h, hv, selectorExpr, exprTokens]

theorem clashRowTokens_eq (q : Nat) (i : Fin (q + 1)) :
    clashRowTokens q i.val =
      exprTokens Fin.val (Expr.disjoin (List.ofFn (clashPairExpr q i))) := by
  rw [exprTokens_disjoin, forestTokens_ofFn]
  simp only [clashRowTokens, forTokens_eq_ofFn, List.length_ofFn]
  apply congrArg (fun xs : List (List Token) => xs.flatten ++ closeOr (q + 1))
  apply congrArg List.ofFn
  funext j
  exact clashPairTokens_eq q i j

theorem clashTokens_eq (q : Nat) :
    clashTokens q = exprTokens Fin.val (clashExpr q) := by
  rw [clashExpr, exprTokens_disjoin, forestTokens_ofFn]
  simp only [clashTokens, forTokens_eq_ofFn, List.length_ofFn]
  apply congrArg (fun xs : List (List Token) => xs.flatten ++ closeOr (q + 1))
  apply congrArg List.ofFn
  funext i
  exact clashRowTokens_eq q i

theorem validityTokens_eq (q : Nat) :
    validityTokens q = exprTokens Fin.val (validityExpr q) := by
  simp [validityTokens, validityExpr, exprTokens, nonemptyTokens_eq,
    clashTokens_eq, List.append_assoc]

theorem presenceTokens_eq (q n : Nat) :
    presenceTokens q n = exprTokens Fin.val (presenceExpr q n) := by
  rw [presenceExpr, exprTokens_disjoin, forestTokens_ofFn]
  simp [presenceTokens, forTokens_eq_ofFn, selectorExpr, exprTokens]

section Symbols

variable {A : Type*} [DecidableEq A]

def payloadSymbolTokens (q : Nat) (f : Bool → A) (i : Nat) (a : Option A) : List Token :=
  [.input (q + 1 + i), .const (decide (some (f true) = a)), .and,
    .input (q + 1 + i), .not, .const (decide (some (f false) = a)), .and, .or]

theorem payloadSymbolTokens_eq (q : Nat) (f : Bool → A) (i : Fin q) (a : Option A) :
    payloadSymbolTokens q f i.val a = exprTokens Fin.val (payloadSymbolExpr q f i a) := by
  simp [payloadSymbolExpr, payloadSymbolTokens, exprTokens_mux, payloadExpr,
    exprTokens, muxTokens]

def inputCellTokens (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    List Token :=
  if n < (inputPrefix input).length then [.const (decide (((inputPrefix input)[n]?).map f = a))]
  else if n - (inputPrefix input).length < q then
    muxTokens (presenceTokens q (n - (inputPrefix input).length))
      (payloadSymbolTokens q f (n - (inputPrefix input).length) a)
      [.const (decide ((none : Option A) = a))]
  else [.const (decide ((none : Option A) = a))]

theorem inputCellTokens_eq (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    inputCellTokens q input f n a = exprTokens Fin.val (inputCellExpr q input f n a) := by
  by_cases hp : n < (inputPrefix input).length
  · simp only [inputCellTokens, inputCellExpr, ite_eq_left hp, exprTokens]
  · by_cases hq : n - (inputPrefix input).length < q
    · simp only [inputCellTokens, inputCellExpr, hp, ite_false, hq, ite_true, dite_eq_left]
      rw [exprTokens_mux, ← presenceTokens_eq, ← payloadSymbolTokens_eq]
      rfl
    · simp only [inputCellTokens, inputCellExpr, ite_eq_right hp, ite_eq_right hq,
        dite_eq_right hq, exprTokens]

end Symbols

section Initial

variable (V : NPVerifier)
variable [DecidableEq V.computation.tm.Λ] [DecidableEq V.computation.tm.σ]
variable [∀ k, DecidableEq (V.computation.tm.Γ k)]

def initialCellTokens (input : List Bool) (S : Nat) (k : V.computation.tm.K)
    (i : Fin S) (a : Option (V.computation.tm.Γ k)) : List Token :=
  if h : k = V.computation.tm.k₀ then by
    subst k
    exact inputCellTokens (V.witnessBound.eval input.length) input
      V.computation.inputAlphabet.invFun i.val a
  else [.const (decide ((none : Option (V.computation.tm.Γ k)) = a))]

omit [DecidableEq V.computation.tm.Λ] [DecidableEq V.computation.tm.σ] in
theorem initialCellTokens_eq (input : List Bool) (S : Nat) (k : V.computation.tm.K)
    (i : Fin S) (a : Option (V.computation.tm.Γ k)) :
    initialCellTokens V input S k i a = exprTokens Fin.val (initialCellExpr V input S k i a) := by
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    simpa [initialCellTokens, initialCellExpr] using
      inputCellTokens_eq (V.witnessBound.eval input.length) input
        V.computation.inputAlphabet.invFun i.val a
  · simp [initialCellTokens, initialCellExpr, hk, exprTokens]

def initTokens (input : List Bool) (S : Nat) :
    ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ S → List Token
  | .inl label => [.const (decide (some V.computation.tm.main = label))]
  | .inr (.inl state) => [.const (decide (V.computation.tm.initialState = state))]
  | .inr (.inr ⟨k, i, a⟩) => initialCellTokens V input S k i a

theorem initTokens_eq (input : List Bool) (S : Nat)
    (bit : ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ S) :
    initTokens V input S bit = exprTokens Fin.val (initExpr V input S bit) := by
  rcases bit with label | (state | ⟨k, i, a⟩)
  · rfl
  · rfl
  · exact initialCellTokens_eq V input S k i a

theorem initTokens_length_le (input : List Bool) (S : Nat)
    (bit : ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ S) :
    (initTokens V input S bit).length ≤ 8 * (V.witnessBound.eval input.length + 1) + 15 := by
  rw [initTokens_eq, exprTokens_length]
  exact size_initExpr_le V input S bit

end Initial

theorem validityTokens_length_le (q : Nat) : (validityTokens q).length ≤ 12 * (q + 1) ^ 2 := by
  rw [validityTokens_eq, exprTokens_length]
  exact size_validityExpr_le q

noncomputable section Frame

open VerifierCircuit

local instance labelDecidable (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance stateDecidable (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def configurationBody (V : NPVerifier) (input : List Bool) (j : Nat) : List Token :=
  if hj : j < width V input then
    initTokens V input (capacity V input.length) ((bitEquiv V input).symm ⟨j, hj⟩)
  else []

theorem configurationBody_index (V : NPVerifier) (input : List Bool) (bit : Bit V input) :
    configurationBody V input (bitEquiv V input bit).val =
      initTokens V input (capacity V input.length) bit := by
  rw [configurationBody, dite_eq_left (bitEquiv V input bit).isLt]
  change initTokens V input (capacity V input.length)
    ((bitEquiv V input).symm (bitEquiv V input bit)) = _
  rw [Equiv.symm_apply_apply]

theorem configurationBody_label (V : NPVerifier) (input : List Bool)
    (label : Option V.computation.tm.Λ) :
    configurationBody V input ((indexing V).labels label).val =
      [.const (decide (some V.computation.tm.main = label))] := by
  simpa only [bitEquiv, ConfigIndex.Indexing.configIndex_label, initTokens] using
    configurationBody_index V input (.inl label)

theorem configurationBody_state (V : NPVerifier) (input : List Bool)
    (state : V.computation.tm.σ) :
    configurationBody V input ((indexing V).labelCount + ((indexing V).states state).val) =
      [.const (decide (V.computation.tm.initialState = state))] := by
  simpa only [bitEquiv, ConfigIndex.Indexing.configIndex_state, initTokens] using
    configurationBody_index V input (.inr (.inl state))

theorem configurationBody_cell (V : NPVerifier) (input : List Bool)
    (k : V.computation.tm.K) (i : Fin (capacity V input.length))
    (a : Option (V.computation.tm.Γ k)) :
    configurationBody V input ((indexing V).labelCount + (indexing V).stateCount +
      i.val * (indexing V).symbolCount + ((indexing V).symbols ⟨k, a⟩).val) =
      initialCellTokens V input (capacity V input.length) k i a := by
  simpa only [bitEquiv, ConfigIndex.Indexing.configIndex_cell, initTokens] using
    configurationBody_index V input (.inr (.inr ⟨k, i, a⟩))

def initializationTokens (V : NPVerifier) (input : List Bool) : List Token :=
  forTokens (width V input) (configurationBody V input) ++
    validityTokens (V.witnessBound.eval input.length)

def tokenBound (V : NPVerifier) (input : List Bool) : Nat :=
  width V input * (8 * (V.witnessBound.eval input.length + 1) + 15) +
    12 * (V.witnessBound.eval input.length + 1) ^ 2

theorem initializationTokens_eq (V : NPVerifier) (input : List Bool) :
    initializationTokens V input =
      forestTokens Fin.val (List.ofFn (initialExpressions V input)) := by
  rw [forestTokens_ofFn, List.ofFn_succ']
  simp only [List.concat_eq_append, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  simp only [initialExpressions, Fin.lastCases_castSucc, Fin.lastCases_last]
  simp only [initializationTokens, forTokens_eq_ofFn, configurationBody, Fin.isLt, dite_eq_left]
  rw [validityTokens_eq]
  apply congrArg (fun xs : List (List Token) => xs.flatten ++
    exprTokens Fin.val (validityExpr (V.witnessBound.eval input.length)))
  apply congrArg List.ofFn
  funext i
  exact initTokens_eq V input (capacity V input.length) ((bitEquiv V input).symm i)

theorem initializationTokens_length (V : NPVerifier) (input : List Bool) :
    (initializationTokens V input).length = Batch.cost (List.ofFn (initialExpressions V input)) := by
  rw [initializationTokens_eq, forestTokens_length]

theorem initialization_inputBits (V : NPVerifier) (input : List Bool) (start : Nat) :
    PostfixModel.inputBits start (initializationTokens V input) =
      encodeWords [start, Batch.cost (List.ofFn (initialExpressions V input))] ++
        tokenBits (initializationTokens V input) := by
  simp only [PostfixModel.inputBits, initializationTokens_length]

theorem initializationTokens_length_le (V : NPVerifier) (input : List Bool) :
    (initializationTokens V input).length ≤ tokenBound V input := by
  have h := forTokens_length_le (width V input) (configurationBody V input)
    (8 * (V.witnessBound.eval input.length + 1) + 15) (by
      intro j hj
      simp only [configurationBody, dite_eq_left hj]
      exact initTokens_length_le V input (capacity V input.length) ((bitEquiv V input).symm ⟨j, hj⟩))
  simpa only [initializationTokens, List.length_append, tokenBound] using
    Nat.add_le_add h (validityTokens_length_le (V.witnessBound.eval input.length))

theorem initializationTokens_compile (V : NPVerifier) (input : List Bool) (start : Nat)
    (roots : List Nat) :
    compileTokens start roots (initializationTokens V input) =
      some (start + Batch.cost (List.ofFn (initialExpressions V input)),
        (Batch.roots start (List.ofFn (initialExpressions V input))).reverse ++ roots,
        Batch.gates Fin.val start (List.ofFn (initialExpressions V input))) := by
  rw [initializationTokens_eq]
  exact compile_forestTokens _ _ _ _

theorem initialization_tokenWords_bounded (V : NPVerifier) (input : List Bool)
    (word : Nat) (h : word ∈ tokenWords (initializationTokens V input)) :
    word ≤ max 5 (2 * V.witnessBound.eval input.length + 1) := by
  rw [initializationTokens_eq] at h
  exact forest_tokenWords_bounded Fin.val _ _ (fun i => i.isLt) word h

theorem initialization_tokenBits_length_le (V : NPVerifier) (input : List Bool) :
    (tokenBits (initializationTokens V input)).length ≤
      2 * tokenBound V input * (2 * V.witnessBound.eval input.length + 7) := by
  have hw := tokenWords_length_le (initializationTokens V input)
  have ht := initializationTokens_length_le V input
  have hb := encodeWords_length_le (tokenWords (initializationTokens V input))
    (2 * V.witnessBound.eval input.length + 6) (by
      intro word hm
      have hh := initialization_tokenWords_bounded V input word hm
      have hm' : max 5 (2 * V.witnessBound.eval input.length + 1) ≤
          2 * V.witnessBound.eval input.length + 6 := by omega
      exact hh.trans hm')
  have hwords : (tokenWords (initializationTokens V input)).length ≤ 2 * tokenBound V input :=
    hw.trans (Nat.mul_le_mul_left 2 ht)
  exact hb.trans (Nat.mul_le_mul_right _ hwords)

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def clean (ambient : σ) : State σ := ((ambient, false), none)

def emitted (output count : K) (base : K → List Bool) (tokens : List Token) : K → List Bool :=
  Function.update (Function.update base output ((tokenBits tokens).reverse ++ base output))
    count (List.replicate tokens.length true ++ base count)

@[simp] theorem emitted_output (output count : K) (hne : output ≠ count)
    (base : K → List Bool) (tokens : List Token) :
    emitted output count base tokens output = (tokenBits tokens).reverse ++ base output := by
  simp [emitted, hne]

@[simp] theorem emitted_count (output count : K) (base : K → List Bool) (tokens : List Token) :
    emitted output count base tokens count = List.replicate tokens.length true ++ base count := by
  simp [emitted]

theorem emitted_other (output count k : K) (ho : k ≠ output) (hc : k ≠ count)
    (base : K → List Bool) (tokens : List Token) : emitted output count base tokens k = base k := by
  simp [emitted, ho, hc]

theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords]

theorem emitted_append (output count : K) (hne : output ≠ count)
    (base : K → List Bool) (first second : List Token) :
    emitted output count (emitted output count base first) second =
      emitted output count base (first ++ second) := by
  funext k
  by_cases ho : k = output
  · subst k
    simp [emitted, hne, tokenBits_append, List.reverse_append, List.append_assoc]
  · by_cases hc : k = count
    · subst k
      have hr : List.replicate second.length true ++ List.replicate first.length true =
          List.replicate (first.length + second.length) true := by
        rw [← List.replicate_add, Nat.add_comm]
      simp only [emitted_count, List.length_append, ← List.append_assoc, hr]
    · simp [emitted, ho, hc]

@[simp] theorem emitted_nil (output count : K) (base : K → List Bool) :
    emitted output count base [] = base := by
  simp [emitted, tokenBits, tokenWords, encodeWords]

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

def literal (output count : K) (tokens : List Token)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  pushWord output (tokenBits tokens)
    (pushWord count (List.replicate tokens.length true) continuation)

theorem stepAux_literal (output count : K) (hne : output ≠ count)
    (tokens : List Token) (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (state : State σ) (base : K → List Bool) :
    TM2.stepAux (literal output count tokens continuation) state base =
      TM2.stepAux continuation state (emitted output count base tokens) := by
  simp [literal, stepAux_pushWord, emitted, Ne.symm hne]

namespace Input

inductive Label where
  | tag | scan | emit (b : Bool) | restore
  deriving DecidableEq

instance : Fintype Label where
  elems := { .tag, .scan, .emit false, .emit true, .restore }
  complete l := by cases l with
    | emit b => cases b <;> simp
    | tag => simp
    | scan => simp
    | restore => simp

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .tag => pushWord (slots 2) (encodeWord 5)
      (.push (slots 3) (fun _ => true) (.goto fun _ => labels .scan))
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) false
      (fun _ b => labels (.emit b)) (labels .restore)
  | .emit b => MachineTransducerCopy.emitter (slots 2) (fun (_ : Bool) _ => false)
      (fun _ b => [b]) (labels .scan) false b
  | .restore => Reduction.MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) exit

def steps (n : Nat) : Nat := 3 * (n + 1) + 3

private theorem identity_output (xs : List Bool) (control : Bool) :
    Reduction.MachineTransducer.output (fun (_ : Bool) _ => false)
      (fun _ b => [b]) control xs = xs := by
  induction xs generalizing control with
  | nil => rfl
  | cons b xs ih => simp [Reduction.MachineTransducer.output, ih]

theorem trace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (sourceWord : base (slots 0) = encodeWord n) (scratchEmpty : base (slots 1) = [])
    (ambient : σ) :
    (advance (TM2.step program))^[steps n]
      (some ⟨some (labels .tag), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 2) (slots 3) base [.input n]⟩ := by
  let tagged := Function.update (Function.update base (slots 2)
    ((encodeWord 5).reverse ++ base (slots 2))) (slots 3) (true :: base (slots 3))
  have htag : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tag), clean ambient, base⟩) =
      some ⟨some (labels .scan), clean ambient, tagged⟩ := by
    change some (TM2.stepAux (program (labels .tag)) _ _) = _
    rw [atLabels, statement, stepAux_pushWord]
    simp [TM2.stepAux, tagged, slots.injective.eq_iff]
  have hs : tagged (slots 0) = encodeWord n := by
    simpa [tagged, slots.injective.eq_iff] using sourceWord
  have ht : tagged (slots 1) = [] := by
    simpa [tagged, slots.injective.eq_iff] using scratchEmpty
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) false (fun (_ : Bool) _ => false) (fun _ b => [b])
    (labels .scan) (labels .restore) (fun _ b => labels (.emit b)) exit program
    (atLabels .scan)
    (fun (control symbol : Bool) => by
      simpa only [statement, MachineTransducerCopy.emitter] using (atLabels (Label.emit symbol)))
    (atLabels .restore) tagged ht ambient false none
  rw [hs, encodeWord_length, identity_output] at hcopy
  have hout : Function.update tagged (slots 2) ((encodeWord n).reverse ++ tagged (slots 2)) =
      emitted (slots 2) (slots 3) base [.input n] := by
    funext k
    by_cases ho : k = slots 2
    · subst k
      simp [tagged, emitted, tokenBits, tokenWords, Token.words, encodeWords,
        slots.injective.eq_iff, List.reverse_append, List.append_assoc]
    · by_cases hc : k = slots 3
      · subst k
        simp [tagged, emitted, slots.injective.eq_iff]
      · simp [tagged, emitted, ho, hc]
  rw [hout] at hcopy
  have h := chain htag hcopy
  simpa only [steps, clean, Nat.add_comm 1] using h

end Input

namespace Pair

def leftMap : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 3], by decide⟩
def rightMap : Fin 4 ↪ Fin 6 := ⟨![1, 0, 2, 3], by decide⟩
def inputLeftMap : Fin 4 ↪ Fin 6 := ⟨![0, 2, 4, 5], by decide⟩
def inputRightMap : Fin 4 ↪ Fin 6 := ⟨![1, 2, 4, 5], by decide⟩

inductive Label where
  | left (l : MachineUnaryLessAt.Label)
  | right (l : MachineUnaryLessAt.Label)
  | branchLeft | branchRight | diagonal
  | inputLeft (l : Input.Label)
  | inputRight (l : Input.Label)
  | conjunction
  deriving DecidableEq, Fintype

def choose (yes no : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .branch (fun s => s.1.2)
    (.load (fun s => clean s.1.1) (.goto fun _ => yes))
    (.load (fun s => clean s.1.1) (.goto fun _ => no))

theorem stepAux_choose (yes no : Λ) (base : K → List Bool) (ambient : σ) (flag : Bool) :
    TM2.stepAux (choose yes no) ((ambient, flag), none) base =
      ⟨some (if flag then yes else no), clean ambient, base⟩ := by
  cases flag <;> rfl

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .left l => MachineUnaryLessAt.statement (leftMap.trans slots)
      (fun l => labels (.left l)) (some (labels .branchLeft)) l
  | .right l => MachineUnaryLessAt.statement (rightMap.trans slots)
      (fun l => labels (.right l)) (some (labels .branchRight)) l
  | .branchLeft => choose (labels (.inputLeft .tag)) (labels (.right .scan))
  | .branchRight => choose (labels (.inputLeft .tag)) (labels .diagonal)
  | .diagonal => literal (slots 4) (slots 5) [.const false]
      (Reduction.MachineTransfer.exitAt (slots 4) exit)
  | .inputLeft l => Input.statement (inputLeftMap.trans slots)
      (fun l => labels (.inputLeft l)) (some (labels (.inputRight .tag))) l
  | .inputRight l => Input.statement (inputRightMap.trans slots)
      (fun l => labels (.inputRight l)) (some (labels .conjunction)) l
  | .conjunction => literal (slots 4) (slots 5) [.and]
      (Reduction.MachineTransfer.exitAt (slots 4) exit)

def offSteps (i j : Nat) : Nat := Input.steps i + Input.steps j + 1

theorem offTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (i j : Nat)
    (leftWord : base (slots 0) = encodeWord i) (rightWord : base (slots 1) = encodeWord j)
    (leftEmpty : base (slots 2) = []) (ambient : σ) :
    (advance (TM2.step program))^[offSteps i j]
      (some ⟨some (labels (.inputLeft .tag)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 4) (slots 5) base [.input i, .input j, .and]⟩ := by
  have hi := Input.trace (inputLeftMap.trans slots) (fun l => labels (.inputLeft l))
    (some (labels (.inputRight .tag))) program (fun _ => atLabels _)
    base i leftWord leftEmpty ambient
  change (advance (TM2.step program))^[Input.steps i]
    (some ⟨some (labels (.inputLeft .tag)), clean ambient, base⟩) =
    some ⟨some (labels (.inputRight .tag)), clean ambient,
      emitted (slots 4) (slots 5) base [.input i]⟩ at hi
  let afterLeft := emitted (slots 4) (slots 5) base [.input i]
  have hjWord : afterLeft (slots 1) = encodeWord j := by
    simpa [afterLeft, emitted, slots.injective.eq_iff] using rightWord
  have hjScratch : afterLeft (slots 2) = [] := by
    simpa [afterLeft, emitted, slots.injective.eq_iff] using leftEmpty
  have hj := Input.trace (inputRightMap.trans slots) (fun l => labels (.inputRight l))
    (some (labels .conjunction)) program (fun _ => atLabels _)
    afterLeft j hjWord hjScratch ambient
  change (advance (TM2.step program))^[Input.steps j]
    (some ⟨some (labels (.inputRight .tag)), clean ambient, afterLeft⟩) =
    some ⟨some (labels .conjunction), clean ambient,
      emitted (slots 4) (slots 5) afterLeft [.input j]⟩ at hj
  let afterRight := emitted (slots 4) (slots 5) afterLeft [.input j]
  have hand : (advance (TM2.step program))^[1]
      (some ⟨some (labels .conjunction), clean ambient, afterRight⟩) =
      some ⟨exit, clean ambient, emitted (slots 4) (slots 5) afterRight [.and]⟩ := by
    change some (TM2.stepAux (program (labels .conjunction)) _ _) = _
    rw [atLabels, statement, stepAux_literal _ _ (slots.injective.ne (by decide))]
    cases exit <;> rfl
  have h := chain (chain hi hj) hand
  simp only [afterRight, afterLeft,
    emitted_append (slots 4) (slots 5) (slots.injective.ne (by decide : (4 : Fin 6) ≠ 5)),
    List.singleton_append] at h
  exact h

def steps (i j : Nat) : Nat := MachineUnaryLessAt.steps i j + 1 +
  if i < j then offSteps i j else
    MachineUnaryLessAt.steps j i + 1 + if j < i then offSteps i j else 1

theorem trace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (i j : Nat)
    (leftWord : base (slots 0) = encodeWord i) (rightWord : base (slots 1) = encodeWord j)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = []) (ambient : σ) :
    (advance (TM2.step program))^[steps i j]
      (some ⟨some (labels (.left .scan)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 4) (slots 5) base (clashPairTokens i j)⟩ := by
  have hl := MachineUnaryLessAt.lessThanTrace (leftMap.trans slots)
    (fun l => labels (.left l)) (some (labels .branchLeft)) program (fun _ => atLabels _)
    base i j [] [] (by simpa [leftMap] using leftWord) (by simpa [leftMap] using rightWord)
    leftEmpty rightEmpty ambient false none
  change (advance (TM2.step program))^[MachineUnaryLessAt.steps i j]
    (some ⟨some (labels (.left .scan)), clean ambient, base⟩) =
    some ⟨some (labels .branchLeft), ((ambient, decide (i < j)), none), base⟩ at hl
  have hr := MachineUnaryLessAt.lessThanTrace (rightMap.trans slots)
    (fun l => labels (.right l)) (some (labels .branchRight)) program (fun _ => atLabels _)
    base j i [] [] (by simpa [rightMap] using rightWord) (by simpa [rightMap] using leftWord)
    leftEmpty rightEmpty ambient false none
  change (advance (TM2.step program))^[MachineUnaryLessAt.steps j i]
    (some ⟨some (labels (.right .scan)), clean ambient, base⟩) =
    some ⟨some (labels .branchRight), ((ambient, decide (j < i)), none), base⟩ at hr
  have hbl : (advance (TM2.step program))^[1]
      (some ⟨some (labels .branchLeft), ((ambient, decide (i < j)), none), base⟩) =
      some ⟨some (if i < j then labels (.inputLeft .tag) else labels (.right .scan)),
        clean ambient, base⟩ := by
    change some (TM2.stepAux (program (labels .branchLeft)) _ _) = _
    rw [atLabels, statement, stepAux_choose]
    simp
  have hbr : (advance (TM2.step program))^[1]
      (some ⟨some (labels .branchRight), ((ambient, decide (j < i)), none), base⟩) =
      some ⟨some (if j < i then labels (.inputLeft .tag) else labels .diagonal),
        clean ambient, base⟩ := by
    change some (TM2.stepAux (program (labels .branchRight)) _ _) = _
    rw [atLabels, statement, stepAux_choose]
    simp
  have hoff := offTrace slots labels exit program atLabels base i j leftWord rightWord leftEmpty ambient
  by_cases hij : i < j
  · rw [ite_eq_left hij] at hbl
    have h := chain (chain hl hbl) hoff
    simpa only [steps, ite_eq_left hij, clashPairTokens, ite_eq_right (Nat.ne_of_lt hij)] using h
  · rw [ite_eq_right hij] at hbl
    by_cases hji : j < i
    · rw [ite_eq_left hji] at hbr
      have h := chain (chain (chain (chain hl hbl) hr) hbr) hoff
      simpa only [steps, ite_eq_right hij, ite_eq_left hji, clashPairTokens,
        ite_eq_right (Ne.symm (Nat.ne_of_lt hji)), Nat.add_assoc] using h
    · rw [ite_eq_right hji] at hbr
      have hd : (advance (TM2.step program))^[1]
          (some ⟨some (labels .diagonal), clean ambient, base⟩) =
          some ⟨exit, clean ambient, emitted (slots 4) (slots 5) base [.const false]⟩ := by
        change some (TM2.stepAux (program (labels .diagonal)) _ _) = _
        rw [atLabels, statement, stepAux_literal _ _ (slots.injective.ne (by decide))]
        cases exit <;> rfl
      have heq : i = j := by omega
      have h := chain (chain (chain (chain hl hbl) hr) hbr) hd
      simpa only [steps, ite_eq_right hij, ite_eq_right hji, clashPairTokens,
        ite_eq_left heq, Nat.add_assoc] using h

theorem steps_le (i j : Nat) : steps i j ≤ 12 * (i + j + 2) := by
  unfold steps offSteps Input.steps MachineUnaryLessAt.steps
  have h₁ := Nat.min_le_left i j
  have h₂ := Nat.min_le_left j i
  split <;> (try split) <;> omega

end Pair

namespace Row

def pairMap : Fin 6 ↪ Fin 7 := ⟨![1, 2, 3, 4, 5, 6], by decide⟩

inductive Label where
  | guard
  | pair (l : Pair.Label)
  | increment
  deriving DecidableEq, Fintype

def statement (slots : Fin 7 ↪ K) (labels : Label → Λ) (done : Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (slots 0) (labels (.pair (.left .scan))) done
  | .pair l => Pair.statement (pairMap.trans slots) (fun l => labels (.pair l))
      (some (labels .increment)) l
  | .increment => .push (slots 2) (fun _ => true) (.goto fun _ => labels .guard)

def frame (slots : Fin 7 ↪ K) (base : K → List Bool) (remaining current : Nat) : K → List Bool :=
  Function.update (Function.update base (slots 0) (encodeWord remaining)) (slots 2) (encodeWord current)

@[simp] theorem frame_current (slots : Fin 7 ↪ K) (base : K → List Bool) (r j : Nat) :
    frame slots base r j (slots 2) = encodeWord j := by simp [frame]

@[simp] theorem frame_remaining (slots : Fin 7 ↪ K) (base : K → List Bool) (r j : Nat) :
    frame slots base r j (slots 0) = encodeWord r := by simp [frame, slots.injective.eq_iff]

theorem counter_frame (slots : Fin 7 ↪ K) (base : K → List Bool) (r r' j : Nat) :
    MachineUnaryCounter.counterTapes (slots 0) (frame slots base r j) r' [] =
      frame slots base r' j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [MachineUnaryCounter.counterTapes, frame, slots.injective.eq_iff]
  · by_cases h₂ : k = slots 2 <;> simp [MachineUnaryCounter.counterTapes, frame, h₀, h₂]

theorem emitted_frame (slots : Fin 7 ↪ K) (base : K → List Bool) (r j : Nat) (tokens : List Token) :
    emitted (slots 5) (slots 6) (frame slots base r j) tokens =
      frame slots (emitted (slots 5) (slots 6) base tokens) r j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [emitted, frame, slots.injective.eq_iff]
  · by_cases h₂ : k = slots 2
    · subst k; simp [emitted, frame, slots.injective.eq_iff]
    · by_cases h₅ : k = slots 5
      · subst k; simp [emitted, frame, slots.injective.eq_iff]
      · by_cases h₆ : k = slots 6
        · subst k; simp [emitted, frame, slots.injective.eq_iff]
        · simp [emitted, frame, h₀, h₂, h₅, h₆]

theorem increment_frame (slots : Fin 7 ↪ K) (base : K → List Bool) (r j : Nat) :
    Function.update (frame slots base r j) (slots 2) (true :: encodeWord j) =
      frame slots base r (j + 1) := by
  simp [frame, encodeWord, List.replicate_succ]

def tokens (count i start : Nat) : List Token :=
  forTokens count (fun j => clashPairTokens i (start + j))

theorem tokens_zero (i start : Nat) : tokens 0 i start = [] := rfl

theorem tokens_succ (count i start : Nat) :
    tokens (count + 1) i start = clashPairTokens i start ++ tokens count i (start + 1) := by
  rw [tokens, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append (clashPairTokens i start))
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

def steps : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | count + 1, i, start => 1 + Pair.steps i start + 1 + steps count i (start + 1)

theorem trace (slots : Fin 7 ↪ K) (labels : Label → Λ) (done : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels done l)
    (base : K → List Bool) (count i start : Nat)
    (leftWord : base (slots 1) = encodeWord i)
    (leftEmpty : base (slots 3) = []) (rightEmpty : base (slots 4) = []) (ambient : σ) :
    (advance (TM2.step program))^[steps count i start]
      (some ⟨some (labels .guard), clean ambient, frame slots base count start⟩) =
      some ⟨some done, clean ambient,
        frame slots (emitted (slots 5) (slots 6) base (tokens count i start)) 0 (start + count)⟩ := by
  induction count generalizing base start with
  | zero =>
    have h := MachineUnaryCounter.guardTrace_zero (slots 0) (labels .guard)
      (labels (.pair (.left .scan))) done program (atLabels .guard)
      (frame slots base 0 start) [] (ambient, false) none
    simpa only [counter_frame, steps, tokens_zero, emitted_nil, Nat.add_zero, clean] using h
  | succ count ih =>
    have hg := MachineUnaryCounter.guardTrace_succ (slots 0) (labels .guard)
      (labels (.pair (.left .scan))) done program (atLabels .guard)
      (frame slots base count start) count [] (ambient, false) none
    simp only [counter_frame] at hg
    have hiWord : frame slots base count start (slots 1) = encodeWord i := by
      simpa [frame, slots.injective.eq_iff] using leftWord
    have hsLeft : frame slots base count start (slots 3) = [] := by
      simpa [frame, slots.injective.eq_iff] using leftEmpty
    have hsRight : frame slots base count start (slots 4) = [] := by
      simpa [frame, slots.injective.eq_iff] using rightEmpty
    have hp := Pair.trace (pairMap.trans slots) (fun l => labels (.pair l))
      (some (labels .increment)) program (fun _ => atLabels _)
      (frame slots base count start) i start hiWord (frame_current slots base count start)
      hsLeft hsRight ambient
    change (advance (TM2.step program))^[Pair.steps i start]
      (some ⟨some (labels (.pair (.left .scan))), clean ambient, frame slots base count start⟩) =
      some ⟨some (labels .increment), clean ambient,
        emitted (slots 5) (slots 6) (frame slots base count start) (clashPairTokens i start)⟩ at hp
    rw [emitted_frame] at hp
    let nextBase := emitted (slots 5) (slots 6) base (clashPairTokens i start)
    have hn : (advance (TM2.step program))^[1]
        (some ⟨some (labels .increment), clean ambient, frame slots nextBase count start⟩) =
        some ⟨some (labels .guard), clean ambient, frame slots nextBase count (start + 1)⟩ := by
      change some (TM2.stepAux (program (labels .increment)) _ _) = _
      rw [atLabels, statement]
      simp only [TM2.stepAux, frame_current, increment_frame]
    have hni : nextBase (slots 1) = encodeWord i := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using leftWord
    have hnl : nextBase (slots 3) = [] := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using leftEmpty
    have hnr : nextBase (slots 4) = [] := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using rightEmpty
    have hr := ih nextBase (start + 1) hni hnl hnr
    have h := chain (chain (chain hg hp) hn) hr
    rw [show start + 1 + count = start + (count + 1) by omega] at h
    simp only [nextBase,
      emitted_append (slots 5) (slots 6) (slots.injective.ne (by decide : (5 : Fin 7) ≠ 6)),
      ← tokens_succ] at h
    exact h

theorem steps_le (count i start B : Nat) (hB : i + start + count ≤ B) :
    steps count i start ≤ count * (12 * (B + 2) + 2) + 1 := by
  induction count generalizing start with
  | zero => simp [steps]
  | succ count ih =>
    have hr := ih (start + 1) (by omega)
    have hp := Pair.steps_le i start
    have hpos : i + start + 2 ≤ B + 2 := by omega
    have hm := Nat.mul_le_mul_left 12 hpos
    rw [steps, Nat.succ_mul]
    omega

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
