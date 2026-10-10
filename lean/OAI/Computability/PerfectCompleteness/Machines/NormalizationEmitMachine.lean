import OAI.Computability.PerfectCompleteness.Foundations.NormalizationLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution

namespace OAI


namespace PerfectCompleteness.NormalizationEmitMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution
open NormalizationWords

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Signs) × Option Bool

def clean (ambient : A) (signs : Signs) : State A := ((ambient, signs), none)

def sourceIndex : NameRef → Fin 6
  | .old i => ⟨i.val + 1, by have := i.isLt; omega⟩
  | .fresh _ => 0

theorem sourceIndex_ne_scratch (name : NameRef) : sourceIndex name ≠ 4 := by
  cases name with
  | old i =>
      intro h
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp only [sourceIndex] at hv
      omega
  | fresh i => simp [sourceIndex]

theorem sourceIndex_ne_output (name : NameRef) : sourceIndex name ≠ 5 := by
  cases name with
  | old i =>
      intro h
      have hi := i.isLt
      have hv := congrArg Fin.val h
      simp only [sourceIndex] at hv
      omega
  | fresh i => simp [sourceIndex]

inductive LocalLabel
  | copyOut
  | copyBack
  | emit
  deriving DecidableEq

protected abbrev LocalLabel.enumList : List LocalLabel := [.copyOut, .copyBack, .emit]

protected theorem LocalLabel.enumList_getElem?_ctorIdx_eq (x : LocalLabel) :
    LocalLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem LocalLabel.enumList_nodup : LocalLabel.enumList.Nodup := by decide

instance : Fintype LocalLabel where
  elems := ⟨LocalLabel.enumList, LocalLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def emitSign (output : K) (sign : SignRef) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => signValue state.1.2 sign)
    (.push output (fun _ => true)
      (.push output (fun _ => false) (exitAt output exit)))
    (.push output (fun _ => false) (exitAt output exit))

def emit (output : K) (literal : LiteralRecipe) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  pushWord output (List.replicate (offset literal.name) true ++ [false])
    (emitSign output literal.sign exit)

def localInstruction (tape : Fin 6 → K) (literal : LiteralRecipe)
    (labels : LocalLabel → Λ) (exit : Option Λ) :
    LocalLabel → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyOut => loopAt (tape (sourceIndex literal.name)) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape (sourceIndex literal.name))
      (tape 5) false (labels .copyBack) (some (labels .emit))
  | .emit => emit (tape 5) literal exit

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem stepAux_emit (output : K) (literal : LiteralRecipe) (exit : Option Λ)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat) :
    TM2.stepAux (emit output literal exit) (clean ambient signs)
      (Function.update base output
        (List.replicate (sourceValue names freshBase literal.name) true ++ base output)) =
      ⟨exit, clean ambient signs, Function.update base output
        ((literalBits signs names freshBase literal).reverse ++ base output)⟩ := by
  have nameOrder : nameValue names freshBase literal.name =
      offset literal.name + sourceValue names freshBase literal.name := by
    exact Nat.add_comm _ _
  have swapped : List.replicate (offset literal.name) true ++
      (List.replicate (sourceValue names freshBase literal.name) true ++ base output) =
      List.replicate (sourceValue names freshBase literal.name) true ++
        (List.replicate (offset literal.name) true ++ base output) := by
    calc
      _ = List.replicate
          (offset literal.name + sourceValue names freshBase literal.name) true ++ base output := by
            rw [List.replicate_add, List.append_assoc]
      _ = List.replicate
          (sourceValue names freshBase literal.name + offset literal.name) true ++ base output := by
            rw [Nat.add_comm (offset literal.name) (sourceValue names freshBase literal.name)]
      _ = _ := by rw [List.replicate_add, List.append_assoc]
  unfold emit
  rw [stepAux_pushWord]
  cases hs : signValue signs literal.sign <;> cases exit <;>
    simp [emitSign, clean, TM2.stepAux, exitAt, hs, literalBits,
      NormalizationWords.literalWords, encodeWords, encodeWord, nameOrder,
      List.reverse_append, List.reverse_replicate, List.replicate_add, List.append_assoc,
      -List.replicate_append_replicate] <;>
    rw [swapped]

theorem literalTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (literal : LiteralRecipe) (labels : LocalLabel → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = localInstruction tape literal labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (sourceWord : base (tape (sourceIndex literal.name)) =
      List.replicate (sourceValue names freshBase literal.name) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[2 * (sourceValue names freshBase literal.name + 1) + 1]
      (some ⟨some (labels .copyOut), clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((literalBits signs names freshBase literal).reverse ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have copied := MachineCopy.copyTrace (tape (sourceIndex literal.name)) (tape 5) (tape 4)
    (hd _ _ (sourceIndex_ne_output _)) (hd _ _ (sourceIndex_ne_scratch _))
    (hd 5 4 (by decide)) false (labels .copyOut) (labels .copyBack)
    (some (labels .emit)) program (atLabels .copyOut) (atLabels .copyBack)
    base scratchEmpty (ambient, signs) none
  rw [sourceWord, List.length_replicate] at copied
  have emitted : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emit), clean ambient signs,
        Function.update base (tape 5)
          (List.replicate (sourceValue names freshBase literal.name) true ++ base (tape 5))⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((literalBits signs names freshBase literal).reverse ++ base (tape 5))⟩ := by
    change some (TM2.stepAux (program (labels .emit)) _ _) = _
    rw [atLabels .emit]
    exact congrArg some (stepAux_emit (tape 5) literal exit base ambient signs names freshBase)
  exact joinTrace copied emitted

def result (signs : Signs) (names : Names) (freshBase : Nat)
    (literal : LiteralRecipe) (output : List Bool) : List Bool :=
  (literalBits signs names freshBase literal).reverse ++ output

def cost (names : Names) (freshBase : Nat) (literal : LiteralRecipe) (_ : List Bool) : Nat :=
  2 * (sourceValue names freshBase literal.name + 1) + 1

def commandSteps (names : Names) (freshBase : Nat) (commands : List LiteralRecipe) : Nat :=
  (commands.map (fun literal => 2 * (sourceValue names freshBase literal.name + 1) + 1)).sum

theorem resultOf_eq (signs : Signs) (names : Names) (freshBase : Nat)
    (commands : List LiteralRecipe) (output : List Bool) :
    MachineFiniteSequence.resultOf (result signs names freshBase) commands output =
      (commands.flatMap (literalBits signs names freshBase)).reverse ++ output := by
  induction commands generalizing output with
  | nil => rfl
  | cons literal commands ih =>
      simp only [MachineFiniteSequence.resultOf, ih, result, List.flatMap_cons,
        List.reverse_append, List.append_assoc]

theorem sequenceSteps_eq (signs : Signs) (names : Names) (freshBase : Nat)
    (commands : List LiteralRecipe) (output : List Bool) :
    MachineFiniteSequence.steps (result signs names freshBase) (cost names freshBase)
      commands output = commandSteps names freshBase commands := by
  induction commands generalizing output with
  | nil => rfl
  | cons literal commands ih =>
      simp only [MachineFiniteSequence.steps, ih, commandSteps, List.map_cons,
        List.sum_cons, cost]

theorem sourceValue_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (name : NameRef) : sourceValue names freshBase name ≤ maximum := by
  cases name with
  | old i => exact nameBounds i
  | fresh i => exact freshBound

theorem commandSteps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (commands : List LiteralRecipe) :
    commandSteps names freshBase commands ≤ commands.length * (2 * maximum + 3) := by
  induction commands with
  | nil => simp [commandSteps]
  | cons literal commands ih =>
      have current := sourceValue_le names freshBase maximum freshBound nameBounds literal.name
      simp only [commandSteps, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

abbrev Labels (commands : List LiteralRecipe) :=
  MachineFiniteSequence.Label (fun _ : LiteralRecipe => LocalLabel) commands

def sequenceInstruction (tape : Fin 6 → K) (commands : List LiteralRecipe)
    (labels : Labels commands → Λ) (exit : Option Λ) :
    Labels commands → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  MachineFiniteSequence.instruction (fun _ => LocalLabel) (fun _ => LocalLabel.copyOut)
    (localInstruction tape) commands labels exit

def sequenceEntry (commands : List LiteralRecipe) (labels : Labels commands → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (fun _ => LocalLabel) (fun _ => LocalLabel.copyOut)
    commands labels exit

theorem sequenceTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (commands : List LiteralRecipe) (labels : Labels commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction tape commands labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (sourceWords : ∀ name, base (tape (sourceIndex name)) =
      List.replicate (sourceValue names freshBase name) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[commandSteps names freshBase commands]
      (some ⟨sequenceEntry commands labels exit, clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((commands.flatMap (literalBits signs names freshBase)).reverse ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have native := MachineFiniteSequence.trace (fun _ : LiteralRecipe => LocalLabel)
    (fun _ => LocalLabel.copyOut) (localInstruction tape)
    (result signs names freshBase) (cost names freshBase) program
    (fun _ => True) (fun _ => clean ambient signs)
    (fun output => Function.update base (tape 5) output) commands
    (fun _ _ _ _ => True.intro)
    (fun literal _ localLabels localExit localEquations output _ => by
      have actual := literalTrace tape distinct literal localLabels localExit program
        localEquations (Function.update base (tape 5) output) ambient signs names freshBase
        (by simp [hd (sourceIndex literal.name) 5 (sourceIndex_ne_output literal.name), sourceWords])
        (by simp [hd 4 5 (by decide), scratchEmpty])
      simpa only [cost, result, Function.update_self, Function.update_idem] using actual)
    labels exit atLabels (base (tape 5)) True.intro
  simpa only [sequenceSteps_eq, resultOf_eq, Function.update_eq_self,
    sequenceEntry] using native

abbrev Label := Labels recipe

def main : Label := .inl .copyOut

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  sequenceInstruction tape recipe labels exit

def steps (names : Names) (freshBase : Nat) : Nat := commandSteps names freshBase recipe

theorem steps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum) :
    steps names freshBase ≤ 39 * (2 * maximum + 3) := by
  simpa only [steps, recipe_length] using
    commandSteps_le names freshBase maximum freshBound nameBounds recipe

theorem gadgetTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names) (freshBase : Nat)
    (freshWord : base (tape 0) = List.replicate freshBase true)
    (oldWords : ∀ i, base (tape (sourceIndex (.old i))) = List.replicate (names i) true)
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps names freshBase]
      (some ⟨some (labels main), clean ambient signs, base⟩) =
      some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((bits signs names freshBase).reverse ++ base (tape 5))⟩ := by
  have sources : ∀ name, base (tape (sourceIndex name)) =
      List.replicate (sourceValue names freshBase name) true := by
    intro name
    cases name with
    | old i => exact oldWords i
    | fresh i => exact freshWord
  have trace := sequenceTrace tape distinct recipe labels exit program atLabels
    base ambient signs names freshBase sources scratchEmpty
  have entry : sequenceEntry recipe labels exit = some (labels main) := rfl
  rw [← bits_eq_flatMap] at trace
  simpa only [steps, entry] using trace

def gadgetInTime (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (ambient : A) (signs : Signs) (names : Names)
    (freshBase maximum : Nat)
    (freshWord : base (tape 0) = List.replicate freshBase true)
    (oldWords : ∀ i, base (tape (sourceIndex (.old i))) = List.replicate (names i) true)
    (scratchEmpty : base (tape 4) = [])
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels main), clean ambient signs, base⟩
      (some ⟨exit, clean ambient signs, Function.update base (tape 5)
        ((bits signs names freshBase).reverse ++ base (tape 5))⟩)
      (39 * (2 * maximum + 3)) where
  steps := steps names freshBase
  evals_in_steps := gadgetTrace tape distinct labels exit program atLabels base ambient
    signs names freshBase freshWord oldWords scratchEmpty
  steps_le_m := steps_le names freshBase maximum freshBound nameBounds

theorem label_finite : Finite Label := inferInstance

theorem state_finite [Finite A] : Finite (State A) := inferInstance

end PerfectCompleteness.NormalizationEmitMachine

end OAI
