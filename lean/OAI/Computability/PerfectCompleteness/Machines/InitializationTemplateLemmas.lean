import OAI.Computability.PerfectCompleteness.Machines.PositionLemmas
import OAI.Computability.PerfectCompleteness.Machines.PostfixAlignment
import OAI.Computability.PerfectCompleteness.Machines.TransitionMachine
import OAI.Computability.PerfectCompleteness.Machines.TransitionTemplate
import OAI.Computability.PerfectCompleteness.Machines.VerifierCircuit

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationTemplate

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationTemplate


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceTemplate


open StatementCircuit VerifierCircuit PostfixModel PostfixAlignment InitializationTemplate

local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def headMask (V : NPVerifier) (k : V.computation.tm.K)
    (symbol : Option (V.computation.tm.Γ k)) : Bool := by
  by_cases h : k = V.computation.tm.k₁
  · subst k
    exact decide (some (V.computation.outputAlphabet.invFun true) = symbol)
  · exact decide ((none : Option (V.computation.tm.Γ k)) = symbol)

theorem accepting_label (V : NPVerifier) (S : Nat) (label : Option V.computation.tm.Λ) :
    configEncoding S (accepting V) (.inl label) = decide (none = label) := rfl

theorem accepting_state (V : NPVerifier) (S : Nat) (state : V.computation.tm.σ) :
    configEncoding S (accepting V) (.inr (.inl state)) =
      decide (V.computation.tm.initialState = state) := rfl

theorem accepting_cell (V : NPVerifier) (S : Nat) (k : V.computation.tm.K)
    (i : Fin S) (symbol : Option (V.computation.tm.Γ k)) :
    configEncoding S (accepting V) (.inr (.inr ⟨k, i, symbol⟩)) =
      if i.val = 0 then headMask V k symbol else decide ((none : Option (V.computation.tm.Γ k)) = symbol) := by
  by_cases hk : k = V.computation.tm.k₁
  · subst k
    rcases i with ⟨i, hi⟩
    cases i <;> simp [configEncoding, inputEncoding, accepting, Turing.haltList,
      StackEncoding.encode, headMask]
  · simp [configEncoding, inputEncoding, accepting, Turing.haltList, hk,
      StackEncoding.encode, headMask]

def targetBit (V : NPVerifier) (input : List Bool) (j : Fin (width V input)) : Bool :=
  configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j)

def mismatchTokens (expected : Bool) (wire : Nat) : List Token :=
  if expected then [.input wire, .not] else [.input wire]

def tokens (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) : List Token :=
  [.input (wire (Fin.last (width V input)))] ++
    (List.ofFn fun j : Fin (width V input) =>
      mismatchTokens (targetBit V input j) (wire j.castSucc)).flatten ++
    closeOr (width V input) ++ [.not, .and]

theorem mismatchTokens_eq (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (j : Fin (width V input)) :
    mismatchTokens (targetBit V input j) (wire j.castSucc) =
      exprTokens wire (mismatchExpr V input j) := by
  by_cases h : configEncoding (capacity V input.length) (accepting V)
      ((bitEquiv V input).symm j) = true
  · simp [mismatchTokens, targetBit, mismatchExpr, exprTokens, h]
  · simp [mismatchTokens, targetBit, mismatchExpr, exprTokens, h]

theorem tokens_eq (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    tokens V input wire = exprTokens wire (acceptanceExpr V input) := by
  simp only [acceptanceExpr, exprTokens, exprTokens_disjoin,
    forestTokens_ofFn, List.length_ofFn]
  simp [tokens, mismatchTokens_eq, List.append_assoc]

theorem compile_tokens (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (start : Nat) (oldRoots : List Nat) :
    compileTokens start oldRoots (tokens V input wire) =
      some (start + (acceptanceExpr V input).size,
        (acceptanceExpr V input).root start :: oldRoots,
        (acceptanceExpr V input).gates wire start) := by
  rw [tokens_eq]
  exact compile_exprTokens wire (acceptanceExpr V input) start oldRoots

theorem tokens_length_le (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    (tokens V input wire).length ≤ 3 * width V input + 4 := by
  rw [tokens_eq, exprTokens_length]
  exact acceptanceExpr_size_le V input

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptanceTemplate


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptancePlan


open StatementCircuit TransitionTemplate AcceptanceTemplate
open PostfixModel VerifierCircuit TermMachine

local instance (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def negateIf {K σ : Type} {Γ : K → Type} (condition : Bool) (e : Term Γ σ) : Term Γ σ :=
  if condition then .not e else e

def stateTemplate (V : NPVerifier) (state : V.computation.tm.σ) :
    Global (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ) (σ := V.computation.tm.σ) :=
  .data (negateIf (decide (V.computation.tm.initialState = state)) (.state state))

def cellTemplate (V : NPVerifier) (k : V.computation.tm.K)
    (symbol : Option (V.computation.tm.Γ k)) :
    Global (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ) (σ := V.computation.tm.σ) :=
  .data (.atZero .current
    (negateIf (headMask V k symbol) (.cell k .current symbol))
    (negateIf (decide ((none : Option (V.computation.tm.Γ k)) = symbol))
      (.cell k .current symbol)))

def plan (V : NPVerifier) :
    TransitionMachine.Plan (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ)
      (σ := V.computation.tm.σ) where
  «prefix» :=
    ((List.finRange (indexing V).labelCount).map fun i =>
      (Global.label ((indexing V).labels.symm i),
        decide ((none : Option V.computation.tm.Λ) = (indexing V).labels.symm i))) ++
    ((List.finRange (indexing V).stateCount).map fun i =>
      (stateTemplate V ((indexing V).states.symm i), false))
  cells := (List.finRange (indexing V).symbolCount).map fun i =>
    let symbol := (indexing V).symbols.symm i
    cellTemplate V symbol.1 symbol.2
  carry := false

def mismatchForest (V : NPVerifier) (roots : List Nat) (S : Nat) : List Token :=
  (outputOrder (indexing V) S).flatMap fun bit =>
    mismatchTokens (configEncoding S (accepting V) bit)
      (configWire (indexing V) roots S bit)

theorem label_tokens (V : NPVerifier) (roots : List Nat) (S cursor : Nat)
    (label : Option V.computation.tm.Λ) :
    (Global.label label).tokens (indexing V) roots S cursor ++
      (if decide ((none : Option V.computation.tm.Λ) = label) then [.not] else []) =
    mismatchTokens (configEncoding S (accepting V) (.inl label))
      (configWire (indexing V) roots S (.inl label)) := by
  rw [accepting_label]
  by_cases h : (none : Option V.computation.tm.Λ) = label
  · simp [Global.tokens, configWire, mismatchTokens, h]
  · simp [Global.tokens, configWire, mismatchTokens, h]

theorem state_tokens (V : NPVerifier) (roots : List Nat) (S cursor : Nat)
    (state : V.computation.tm.σ) :
    (stateTemplate V state).tokens (indexing V) roots S cursor =
      mismatchTokens (configEncoding S (accepting V) (.inr (.inl state)))
        (configWire (indexing V) roots S (.inr (.inl state))) := by
  rw [accepting_state]
  by_cases h : V.computation.tm.initialState = state
  · simp [stateTemplate, negateIf, Global.tokens, Term.tokens, configWire, mismatchTokens, h]
  · simp [stateTemplate, negateIf, Global.tokens, Term.tokens, configWire, mismatchTokens, h]

theorem cell_tokens (V : NPVerifier) (roots : List Nat) (S : Nat)
    (i : Fin S) (k : V.computation.tm.K) (symbol : Option (V.computation.tm.Γ k)) :
    (cellTemplate V k symbol).tokens (indexing V) roots S i.val =
      mismatchTokens (configEncoding S (accepting V) (.inr (.inr ⟨k, i, symbol⟩)))
        (configWire (indexing V) roots S (.inr (.inr ⟨k, i, symbol⟩))) := by
  rw [accepting_cell]
  have hS : 0 < S := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  by_cases hi : i.val = 0
  · cases hb : headMask V k symbol <;>
      simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        hS, hi, hb, mismatchTokens, configWire]
  · by_cases hs : (none : Option (V.computation.tm.Γ k)) = symbol
    · simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        i.isLt, hi, hs, mismatchTokens, configWire]
    · simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        i.isLt, hi, hs, mismatchTokens, configWire]

theorem outputTokens_eq (V : NPVerifier) (input : TermMachine.Input) :
    TransitionMachine.outputTokens (indexing V) (plan V) input =
      mismatchForest V input.roots input.capacity := by
  rw [TransitionMachine.outputTokens_eq_blocks]
  simp only [mismatchForest, OutputOrder.outputOrder_eq_blocks, List.flatMap_append,
    List.flatMap_map, List.flatMap_assoc]
  simp only [plan, TransitionMachine.prefixTokens, List.flatMap_append, List.flatMap_map,
    TransitionMachine.cellTokens, TransitionMachine.listTokens,
    TermMachine.globalTokens, TransitionMachine.withCursor_roots,
    TransitionMachine.withCursor_capacity, TransitionMachine.withCursor_cursor,
    TransitionMachine.carriedTokens, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  congr 1
  · congr 1
    · apply List.flatMap_congr
      intro i _
      exact label_tokens V input.roots input.capacity 0 ((indexing V).labels.symm i)
    · apply List.flatMap_congr
      intro i _
      simpa using state_tokens V input.roots input.capacity 0 ((indexing V).states.symm i)
  · apply List.flatMap_congr
    intro i _
    apply List.flatMap_congr
    intro j _
    exact cell_tokens V input.roots input.capacity i
      ((indexing V).symbols.symm j).1 ((indexing V).symbols.symm j).2

theorem mismatchForest_circuit (V : NPVerifier) (input : List Bool) (roots : List Nat) :
    mismatchForest V roots (capacity V input.length) =
      (List.ofFn fun j : Fin (width V input) =>
        mismatchTokens (targetBit V input j) (rootLookup roots j.val)).flatten := by
  simp only [mismatchForest, outputOrder, List.flatMap_def,
    Function.comp_def, configWire, Equiv.apply_symm_apply, targetBit,
    ← List.ofFn_eq_map, List.map_ofFn, bitEquiv]

theorem fullTokens_eq (V : NPVerifier) (input : List Bool) (roots : List Nat) :
    AcceptanceTemplate.tokens V input (fun j => rootLookup roots j.val) =
      [.input (rootLookup roots (width V input))] ++
      TransitionMachine.outputTokens (indexing V) (plan V)
        ⟨0, capacity V input.length, roots⟩ ++
      InitializationTemplate.closeOr (width V input) ++ [.not, .and] := by
  rw [outputTokens_eq, mismatchForest_circuit]
  rfl

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.AcceptancePlan

end

end OAI
