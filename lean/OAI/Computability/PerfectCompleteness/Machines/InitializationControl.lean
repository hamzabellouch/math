import OAI.Computability.PerfectCompleteness.Machines.InitializationTemplateLemmas
import OAI.Computability.PerfectCompleteness.Machines.OutputOrder
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationControl


open Turing PostfixModel VerifierCircuit InitializationTemplate
open Reduction.MachineSubstitution

local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def tokens (V : NPVerifier) : List Token :=
  ((List.finRange (indexing V).labelCount).map fun i =>
    .const (decide (some V.computation.tm.main = (indexing V).labels.symm i))) ++
  ((List.finRange (indexing V).stateCount).map fun i =>
    .const (decide (V.computation.tm.initialState = (indexing V).states.symm i)))

@[simp] theorem tokens_length (V : NPVerifier) :
    (tokens V).length = (indexing V).labelCount + (indexing V).stateCount := by
  simp [tokens]

def cells (V : NPVerifier) (input : List Bool) (S : Nat) : List Token :=
  (List.finRange S).flatMap fun i =>
    (List.finRange (indexing V).symbolCount).flatMap fun j =>
      let symbol := (indexing V).symbols.symm j
      initialCellTokens V input S symbol.1 i symbol.2

theorem configurationTokens_eq (V : NPVerifier) (input : List Bool) :
    (TransitionTemplate.outputOrder (indexing V) (capacity V input.length)).flatMap
      (initTokens V input (capacity V input.length)) =
      forTokens (width V input) (configurationBody V input) := by
  simp only [TransitionTemplate.outputOrder, List.flatMap_def,
    ← List.ofFn_eq_map, List.map_ofFn, Function.comp_def,
    forTokens_eq_ofFn, configurationBody, Fin.isLt, dite_eq_left]
  rfl

private theorem flatten_singletons {α β : Type*} (xs : List α) (f : α → β) :
    (xs.map fun x => [f x]).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem initializationTokens_eq_blocks (V : NPVerifier) (input : List Bool) :
    initializationTokens V input = tokens V ++ cells V input (capacity V input.length) ++
      validityTokens (V.witnessBound.eval input.length) := by
  rw [initializationTokens, ← configurationTokens_eq, OutputOrder.outputOrder_eq_blocks]
  simp [tokens, cells,
    initTokens, List.flatMap_def, List.map_map, Function.comp_def, List.append_assoc,
    flatten_singletons, List.flatten_flatten]


variable {K Λ σ : Type} [DecidableEq K]

structure Ports (K : Type) where
  reversed : K
  count : K
  distinct : reversed ≠ count

def emitted (p : Ports K) (base : K → List Bool) (ts : List Token) : K → List Bool :=
  Function.update
    (Function.update base p.reversed ((tokenBits ts).reverse ++ base p.reversed))
    p.count (List.replicate ts.length true ++ base p.count)

@[simp] theorem emitted_reversed (p : Ports K) (base : K → List Bool) (ts : List Token) :
    emitted p base ts p.reversed = (tokenBits ts).reverse ++ base p.reversed := by
  simp [emitted, p.distinct]

@[simp] theorem emitted_count (p : Ports K) (base : K → List Bool) (ts : List Token) :
    emitted p base ts p.count = List.replicate ts.length true ++ base p.count := by
  simp [emitted]

theorem emitted_other (p : Ports K) (base : K → List Bool) (ts : List Token)
    (k : K) (hr : k ≠ p.reversed) (hc : k ≠ p.count) : emitted p base ts k = base k := by
  simp [emitted, hr, hc]

def exitStatement (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def literalStatement (p : Ports K) (ts : List Token) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ :=
  pushWord p.reversed (tokenBits ts)
    (pushWord p.count (List.replicate ts.length true) (exitStatement exit))

theorem literalStep (p : Ports K) (ts : List Token) (exit : Option Λ)
    (base : K → List Bool) (state : σ) :
    TM2.stepAux (literalStatement p ts exit) state base =
      ⟨exit, state, emitted p base ts⟩ := by
  rw [literalStatement, stepAux_pushWord, stepAux_pushWord]
  cases exit <;>
    simp [exitStatement, TM2.stepAux, emitted, p.distinct.symm]

theorem literalTrace (p : Ports K) (ts : List Token) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (code : program entry = literalStatement p ts exit)
    (base : K → List Bool) (state : σ) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some entry, state, base⟩) =
      some ⟨exit, state, emitted p base ts⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some, TM2.step, code]
  rw [literalStep]

def statement (V : NPVerifier) (p : Ports K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ := literalStatement p (tokens V) exit

theorem trace (V : NPVerifier) (p : Ports K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (code : program entry = statement V p exit)
    (base : K → List Bool) (state : σ) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some entry, state, base⟩) =
      some ⟨exit, state, emitted p base (tokens V)⟩ :=
  literalTrace p (tokens V) entry exit program code base state

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationControl

end

end OAI
