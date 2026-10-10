import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.PCP.NormalizationEmitMachine
import OAI.Computability.BinPacking.PCP.NormalizationReadMachine

namespace OAI

namespace BinPackingCompleteness.NormalizationStream

open BinPackingGames.Foundations Complexity NormalizationWords

def blocks {n : Nat} (freshBase : Nat) : List (Target.Clause n) → List Bool
  | [] => []
  | clause :: clauses =>
      bits (clauseSigns clause) (clauseNames clause) freshBase ++ blocks (freshBase + 4) clauses

theorem blocks_eq_finRange {n : Nat} (clauses : List (Target.Clause n)) (freshBase : Nat) :
    blocks freshBase clauses = (List.finRange clauses.length).flatMap (fun i =>
      bits (clauseSigns clauses[i.val]) (clauseNames clauses[i.val]) (freshBase + 4 * i.val)) := by
  induction clauses generalizing freshBase with
  | nil => simp [blocks]
  | cons clause clauses ih =>
      simp only [blocks, List.length_cons, List.finRange_succ, List.flatMap_cons,
        List.flatMap_map, List.getElem_cons_zero, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
      apply congrArg (fun tail => bits (clauseSigns clause) (clauseNames clause) freshBase ++ tail)
      rw [ih]
      apply List.flatMap_congr
      intro i _
      have address : freshBase + 4 + 4 * i.val = freshBase + 4 * (i.val + 1) := by omega
      simp only [Fin.val_succ, List.getElem_cons_succ, address]

theorem body_eq_blocks (formula : Target.Formula) :
    NormalizationWords.body formula = blocks formula.variables formula.clauses := by
  rw [blocks_eq_finRange]
  rfl

theorem encoded_normalize (formula : Target.Formula) :
    formulaBits (Normalization.normalize formula) =
      encodeWord (formula.variables + 4 * formula.clauses.length) ++
        encodeWord (13 * formula.clauses.length) ++ blocks formula.variables formula.clauses := by
  rw [NormalizationWords.encoded_normalize, body_eq_blocks]

theorem blocks_length_le {n : Nat} (clauses : List (Target.Clause n)) (freshBase : Nat)
    (bound : Nat) (oldBound : n ≤ bound) (freshBound : freshBase + 4 * clauses.length ≤ bound) :
    (blocks freshBase clauses).length ≤ clauses.length * (39 * (bound + 3)) := by
  have literalBound (names : Names) (fresh : Nat) (signs : Signs)
      (hn : ∀ i, names i ≤ bound) (hf : fresh + 3 ≤ bound) (literal : LiteralRecipe) :
      (literalBits signs names fresh literal).length ≤ bound + 3 := by
    have nameBound : nameValue names fresh literal.name ≤ bound := by
      cases h : literal.name with
      | old i => simpa [nameValue, sourceValue, offset, h] using hn i
      | fresh i =>
          have hi := i.isLt
          simp only [nameValue, sourceValue, offset]
          omega
    cases h : signValue signs literal.sign <;>
      simp [literalBits, NormalizationWords.literalWords, h] <;> omega
  have gadgetBound (clause : Target.Clause n) (fresh : Nat) (hf : fresh + 3 ≤ bound) :
      (bits (clauseSigns clause) (clauseNames clause) fresh).length ≤ 39 * (bound + 3) := by
    rw [bits_eq_flatMap]
    have listBound (commands : List LiteralRecipe) :
        (commands.flatMap (literalBits (clauseSigns clause) (clauseNames clause) fresh)).length ≤
          commands.length * (bound + 3) := by
      induction commands with
      | nil => simp
      | cons command commands ih =>
          have hc := literalBound (clauseNames clause) fresh (clauseSigns clause)
            (fun i => Nat.le_trans (clause[i].variableIndex.isLt.le) oldBound) hf command
          simp only [List.flatMap_cons, List.length_append, List.length_cons,
            Nat.add_mul, Nat.one_mul]
          omega
    simpa only [recipe_length] using listBound recipe
  induction clauses generalizing freshBase with
  | nil => simp [blocks]
  | cons clause clauses ih =>
      have head := gadgetBound clause freshBase (by simp only [List.length_cons] at freshBound; omega)
      have tail := ih (freshBase + 4) (by simp only [List.length_cons] at freshBound; omega)
      simp only [blocks, List.length_append, List.length_cons]
      nlinarith

end BinPackingCompleteness.NormalizationStream

namespace BinPackingCompleteness.NormalizationLoopMachine

open Turing
open BinPackingGames.Foundations
open Complexity Complexity.MachineComposition
open BinPackingGames.Reduction.MachineSubstitution
open NormalizationWords

def nameSum {n : Nat} (clause : Target.Clause n) : Nat :=
  clause[0].variableIndex.val + clause[1].variableIndex.val + clause[2].variableIndex.val

def bodySteps {n : Nat} (freshBase : Nat) (clause : Target.Clause n) : Nat :=
  1 + (nameSum clause + 6) + NormalizationEmitMachine.steps (clauseNames clause) freshBase +
    (clause[0].variableIndex.val + 1) + (clause[1].variableIndex.val + 1) +
    (clause[2].variableIndex.val + 1) + 1

def steps {n : Nat} (freshBase : Nat) : List (Target.Clause n) → Nat
  | [] => 1
  | clause :: clauses => bodySteps freshBase clause + steps (freshBase + 4) clauses

theorem bodySteps_le {n : Nat} (freshBase maximum : Nat) (clause : Target.Clause n)
    (nameBound : n ≤ maximum) (freshBound : freshBase ≤ maximum) :
    bodySteps freshBase clause ≤ 84 * maximum + 128 := by
  have oldBounds (i : Fin 3) : clauseNames clause i ≤ maximum :=
    (Nat.le_of_lt clause[i].variableIndex.isLt).trans nameBound
  have emitted := NormalizationEmitMachine.steps_le (clauseNames clause)
    freshBase maximum freshBound oldBounds
  have h0 := oldBounds 0
  have h1 := oldBounds 1
  have h2 := oldBounds 2
  simp only [clauseNames] at h0 h1 h2
  unfold bodySteps nameSum
  omega

theorem steps_le {n : Nat} (freshBase maximum : Nat) (clauses : List (Target.Clause n))
    (nameBound : n ≤ maximum) (freshBound : freshBase + 4 * clauses.length ≤ maximum) :
    steps freshBase clauses ≤ clauses.length * (84 * maximum + 128) + 1 := by
  induction clauses generalizing freshBase with
  | nil => simp [steps]
  | cons clause clauses ih =>
      have head := bodySteps_le freshBase maximum clause nameBound (by
        simp only [List.length_cons] at freshBound
        omega)
      have tail := ih (freshBase + 4) (by
        simp only [List.length_cons] at freshBound
        omega)
      simp only [steps, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Signs) × Option Bool
abbrev clean (ambient : A) (signs : Signs) : State A := NormalizationEmitMachine.clean ambient signs
def reset (ambient : A) : State A := clean ambient (fun _ => false)

def readerIndex : Fin 4 → Fin 9
  | 0 => 0
  | 1 => 4
  | 2 => 5
  | 3 => 6

def emitterIndex : Fin 6 → Fin 9
  | 0 => 1
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 8

def oldIndex (slot : Fin 3) : Fin 9 := ⟨slot.val + 4, by have := slot.isLt; omega⟩

def readerTapes (tape : Fin 9 → K) : Fin 4 → K := fun i => tape (readerIndex i)
def emitterTapes (tape : Fin 9 → K) : Fin 6 → K := fun i => tape (emitterIndex i)

omit [DecidableEq K] in
theorem readerTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (readerTapes tape) :=
  distinct.comp (by decide : Function.Injective readerIndex)

omit [DecidableEq K] in
theorem emitterTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (emitterTapes tape) :=
  distinct.comp (by decide : Function.Injective emitterIndex)

inductive Label
  | guard
  | read (label : NormalizationReadMachine.Label)
  | emit (label : NormalizationEmitMachine.Label)
  | drain (slot : Fin 3)
  | tally
  deriving DecidableEq, Fintype

def afterDrain (labels : Label → Λ) (slot : Fin 3) : Λ :=
  if slot = 0 then labels (.drain 1) else if slot = 1 then labels (.drain 2) else labels .tally

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => reset state.1.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def instruction (tape : Fin 9 → K) (labels : Label → Λ) (done rejected : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard =>
      .pop (tape 2) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isNone)
          (finish done)
          (.branch (fun state => state.2.getD false)
            (finish (some (labels (.read (.field 0))))) (finish rejected)))
  | .read l => NormalizationReadMachine.instruction (readerTapes tape)
      (fun l => labels (.read l)) (some (labels (.emit NormalizationEmitMachine.main))) rejected l
  | .emit l => NormalizationEmitMachine.instruction (emitterTapes tape)
      (fun l => labels (.emit l)) (some (labels (.drain 0))) l
  | .drain slot => MachineDrain.drain (tape (oldIndex slot)) (labels (.drain slot))
      (some (afterDrain labels slot))
  | .tally => pushWord (tape 1) (List.replicate 4 true)
      (pushWord (tape 3) (List.replicate 13 true) (finish (some (labels .guard))))

def loopTapes (tape : Fin 9 → K) (base : K → List Bool) (input : List Bool)
    (freshBase remaining : Nat) (clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    (tape 0) input) (tape 1) (List.replicate freshBase true))
    (tape 2) (List.replicate remaining true)) (tape 3) clauseCounter) (tape 8) output

theorem loopTapes_input (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 0) = input := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_fresh (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 1) =
      List.replicate freshBase true := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_remaining (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 2) =
      List.replicate remaining true := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_count (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 3) =
      clauseCounter := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_output (tape : Fin 9 → K) (base : K → List Bool) (input : List Bool)
    (freshBase remaining : Nat) (clauseCounter output : List Bool) :
    loopTapes tape base input freshBase remaining clauseCounter output (tape 8) = output := by
  simp [loopTapes]

private theorem update_remaining (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining replacement : Nat)
    (clauseCounter output : List Bool) :
    Function.update (loopTapes tape base input freshBase remaining clauseCounter output)
        (tape 2) (List.replicate replacement true) =
      loopTapes tape base input freshBase replacement clauseCounter output := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 2
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_fresh (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining replacement : Nat)
    (clauseCounter output : List Bool) :
    Function.update (loopTapes tape base input freshBase remaining clauseCounter output)
        (tape 1) (List.replicate replacement true) =
      loopTapes tape base input replacement remaining clauseCounter output := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 1
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

private theorem update_count (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output replacement : List Bool) :
    Function.update (loopTapes tape base input freshBase remaining clauseCounter output)
        (tape 3) replacement =
      loopTapes tape base input freshBase remaining replacement output := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 3
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, reset state.1.1, base⟩ := by
  cases exit <;> rfl

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 9 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done rejected l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem guardStep (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), reset ambient,
        loopTapes tape base input freshBase (remaining + 1) clauseCounter output⟩ =
      some ⟨some (labels (.read (.field 0))), reset ambient,
        loopTapes tape base input freshBase remaining clauseCounter output⟩ := by
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, reset, clean, NormalizationEmitMachine.clean,
    loopTapes_remaining tape distinct, List.replicate_succ, update_remaining tape distinct]

theorem emptyStep (input : List Bool) (freshBase : Nat) (clauseCounter output : List Bool) :
    TM2.step program
      ⟨some (labels .guard), reset ambient,
        loopTapes tape base input freshBase 0 clauseCounter output⟩ =
      some ⟨done, reset ambient, loopTapes tape base input freshBase 0 clauseCounter output⟩ := by
  change some (TM2.stepAux (program (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [instruction, TM2.stepAux, reset, clean, NormalizationEmitMachine.clean,
    loopTapes_remaining tape distinct]

theorem tallyStep (input : List Bool) (freshBase remaining : Nat)
    (clauseCounter output : List Bool) (signs : Signs) :
    TM2.step program
      ⟨some (labels .tally), clean ambient signs,
        loopTapes tape base input freshBase remaining clauseCounter output⟩ =
      some ⟨some (labels .guard), reset ambient,
        loopTapes tape base input (freshBase + 4) remaining
          (List.replicate 13 true ++ clauseCounter) output⟩ := by
  have freshEq : List.replicate 4 true ++ List.replicate freshBase true =
      List.replicate (freshBase + 4) true := by
    rw [← List.replicate_add, Nat.add_comm]
  change some (TM2.stepAux (program (labels .tally)) _ _) = _
  rw [atLabels .tally]
  simp only [instruction, stepAux_pushWord, List.reverse_replicate,
    loopTapes_fresh tape distinct, freshEq, update_fresh tape distinct,
    loopTapes_count tape distinct, update_count tape distinct,
    stepAux_finish, clean, NormalizationEmitMachine.clean]

theorem bodyTrace {n : Nat} (clause : Target.Clause n) (suffix : List Bool)
    (freshBase remaining : Nat) (clauseCounter output : List Bool)
    (empty : ∀ i : Fin 9, 4 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[bodySteps freshBase clause]
      (some ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
          freshBase (remaining + 1) clauseCounter output⟩) =
      some ⟨some (labels .guard), reset ambient,
        loopTapes tape base suffix (freshBase + 4) remaining
          (List.replicate 13 true ++ clauseCounter)
          ((bits (clauseSigns clause) (clauseNames clause) freshBase).reverse ++ output)⟩ := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 9) (lo : 4 ≤ i.val := by decide) (hi : i.val ≤ 7 := by decide) :
      base (tape i) = [] := empty i lo hi
  let s₀ := loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
    freshBase remaining clauseCounter output
  let s₁ := NormalizationReadMachine.tapes (readerTapes tape) s₀ suffix
    (NormalizationReadMachine.clauseCounters clause)
  let word := bits (clauseSigns clause) (clauseNames clause) freshBase
  let s₂ := Function.update s₁ (tape 8) (word.reverse ++ output)
  let s₃ := Function.update s₂ (tape 4) []
  let s₄ := Function.update s₃ (tape 5) []
  let s₅ := Function.update s₄ (tape 6) []
  have guard : (advance (TM2.step program))^[1]
      (some ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauseWords clause) ++ suffix)
          freshBase (remaining + 1) clauseCounter output⟩) =
      some ⟨some (labels (.read (.field 0))), reset ambient, s₀⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      guardStep tape distinct labels done rejected program atLabels base ambient
        (encodeWords (clauseWords clause) ++ suffix) freshBase remaining clauseCounter output
  have s₀input : s₀ (tape 0) = encodeWords (clauseWords clause) ++ suffix := by
    simp [s₀, loopTapes, hd]
  have s₀old (i : Fin 9) (hi : i = 4 ∨ i = 5 ∨ i = 6) : s₀ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl <;> simp [s₀, loopTapes, hd, he]
  have initialReader : NormalizationReadMachine.tapes (readerTapes tape) s₀
      (encodeWords (clauseWords clause) ++ suffix) (fun _ => []) = s₀ := by
    have unchanged (i : Fin 9) (hi : i = 4 ∨ i = 5 ∨ i = 6) :
        Function.update s₀ (tape i) [] = s₀ := by
      funext k
      by_cases hk : k = tape i
      · subst k
        simp [s₀old i hi]
      · simp [hk]
    change Function.update (Function.update (Function.update (Function.update s₀
      (tape 0) _) (tape 4) []) (tape 5) []) (tape 6) [] = s₀
    rw [← s₀input, Function.update_eq_self, unchanged 4 (by simp),
      unchanged 5 (by simp), unchanged 6 (by simp)]
  have read := NormalizationReadMachine.clauseTrace (readerTapes tape)
    (readerTapes_injective tape distinct) (fun l => labels (.read l))
    (some (labels (.emit NormalizationEmitMachine.main))) rejected program
    (fun l => atLabels (.read l)) s₀ ambient clause suffix (fun _ => false) none
  rw [initialReader] at read
  have s₁fresh : s₁ (tape 1) = List.replicate freshBase true := by
    simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex, s₀, loopTapes, hd]
  have s₁old (i : Fin 3) :
      s₁ (emitterTapes tape (NormalizationEmitMachine.sourceIndex (.old i))) =
        List.replicate (clauseNames clause i) true := by
    fin_cases i <;>
      simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex,
        emitterTapes, emitterIndex, NormalizationEmitMachine.sourceIndex,
        NormalizationReadMachine.clauseCounters, clauseNames, hd]
  have s₁scratch : s₁ (tape 7) = [] := by
    simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex, s₀, loopTapes, hd, he 7]
  have s₁output : s₁ (tape 8) = output := by
    simp [s₁, NormalizationReadMachine.tapes, readerTapes, readerIndex, s₀, loopTapes, hd]
  have emit := NormalizationEmitMachine.gadgetTrace (emitterTapes tape)
    (emitterTapes_injective tape distinct) (fun l => labels (.emit l))
    (some (labels (.drain 0))) program (fun l => atLabels (.emit l)) s₁ ambient
    (clauseSigns clause) (clauseNames clause) freshBase s₁fresh s₁old s₁scratch
  rw [show emitterTapes tape 5 = tape 8 from rfl, s₁output] at emit
  have s₂old : s₂ (tape 4) = List.replicate clause[0].variableIndex.val true := by
    simpa [s₂, hd 4 8 (by decide), emitterTapes, emitterIndex,
      NormalizationEmitMachine.sourceIndex, clauseNames] using s₁old 0
  have drain₀ : (advance (TM2.step program))^[clause[0].variableIndex.val + 1]
      (some ⟨some (labels (.drain 0)), clean ambient (clauseSigns clause), s₂⟩) =
      some ⟨some (labels (.drain 1)), clean ambient (clauseSigns clause), s₃⟩ := by
    have h := MachineDrain.drainTrace (tape 4) (labels (.drain 0)) (some (labels (.drain 1)))
      program (atLabels (.drain 0)) s₂ (List.replicate clause[0].variableIndex.val true)
      (ambient, clauseSigns clause) none
    have initial : Function.update s₂ (tape 4)
        (List.replicate clause[0].variableIndex.val true) = s₂ := by
      rw [← s₂old]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_replicate, clean, NormalizationEmitMachine.clean, s₃] using h
  have s₃old : s₃ (tape 5) = List.replicate clause[1].variableIndex.val true := by
    simpa [s₃, s₂, hd 5 4 (by decide), hd 5 8 (by decide), emitterTapes, emitterIndex,
      NormalizationEmitMachine.sourceIndex, clauseNames] using s₁old 1
  have drain₁ : (advance (TM2.step program))^[clause[1].variableIndex.val + 1]
      (some ⟨some (labels (.drain 1)), clean ambient (clauseSigns clause), s₃⟩) =
      some ⟨some (labels (.drain 2)), clean ambient (clauseSigns clause), s₄⟩ := by
    have h := MachineDrain.drainTrace (tape 5) (labels (.drain 1)) (some (labels (.drain 2)))
      program (atLabels (.drain 1)) s₃ (List.replicate clause[1].variableIndex.val true)
      (ambient, clauseSigns clause) none
    have initial : Function.update s₃ (tape 5)
        (List.replicate clause[1].variableIndex.val true) = s₃ := by
      rw [← s₃old]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_replicate, clean, NormalizationEmitMachine.clean, s₄] using h
  have s₄old : s₄ (tape 6) = List.replicate clause[2].variableIndex.val true := by
    simpa [s₄, s₃, s₂, hd 6 5 (by decide), hd 6 4 (by decide), hd 6 8 (by decide),
      emitterTapes, emitterIndex, NormalizationEmitMachine.sourceIndex, clauseNames] using s₁old 2
  have drain₂ : (advance (TM2.step program))^[clause[2].variableIndex.val + 1]
      (some ⟨some (labels (.drain 2)), clean ambient (clauseSigns clause), s₄⟩) =
      some ⟨some (labels .tally), clean ambient (clauseSigns clause), s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 6) (labels (.drain 2)) (some (labels .tally))
      program (atLabels (.drain 2)) s₄ (List.replicate clause[2].variableIndex.val true)
      (ambient, clauseSigns clause) none
    have initial : Function.update s₄ (tape 6)
        (List.replicate clause[2].variableIndex.val true) = s₄ := by
      rw [← s₄old]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_replicate, clean, NormalizationEmitMachine.clean, s₅] using h
  have restored : s₅ = loopTapes tape base suffix freshBase remaining clauseCounter
      (word.reverse ++ output) := by
    funext k
    by_cases h8 : k = tape 8
    · subst k
      simp [s₅, s₄, s₃, s₂, loopTapes, hd]
    · by_cases h0 : k = tape 0
      · subst k
        simp [s₅, s₄, s₃, s₂, s₁, NormalizationReadMachine.tapes,
          readerTapes, readerIndex, loopTapes, hd]
      · by_cases h4 : k = tape 4
        · subst k
          simp [s₅, s₄, s₃, loopTapes, hd, he 4]
        · by_cases h5 : k = tape 5
          · subst k
            simp [s₅, s₄, loopTapes, hd, he 5]
          · by_cases h6 : k = tape 6
            · subst k
              simp [s₅, loopTapes, hd, he 6]
            · simp [s₅, s₄, s₃, s₂, s₁, NormalizationReadMachine.tapes,
                readerTapes, readerIndex, s₀, loopTapes, h8, h0, h4, h5, h6,
                Function.update_apply]
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient (clauseSigns clause), s₅⟩) =
      some ⟨some (labels .guard), reset ambient,
        loopTapes tape base suffix (freshBase + 4) remaining
          (List.replicate 13 true ++ clauseCounter) (word.reverse ++ output)⟩ := by
    rw [restored]
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done rejected program atLabels base ambient suffix
        freshBase remaining clauseCounter (word.reverse ++ output) (clauseSigns clause)
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace guard read) emit) drain₀) drain₁) drain₂) tally
  simpa only [bodySteps, nameSum, word] using full

theorem loopTrace {n : Nat} (clauses : List (Target.Clause n)) (suffix : List Bool)
    (freshBase : Nat) (clauseCounter output : List Bool)
    (empty : ∀ i : Fin 9, 4 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps freshBase clauses]
      (some ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauses.flatMap clauseWords) ++ suffix)
          freshBase clauses.length clauseCounter output⟩) =
      some ⟨done, reset ambient,
        loopTapes tape base suffix (freshBase + 4 * clauses.length) 0
          (List.replicate (13 * clauses.length) true ++ clauseCounter)
          ((NormalizationStream.blocks freshBase clauses).reverse ++ output)⟩ := by
  induction clauses generalizing freshBase clauseCounter output with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, List.flatMap_nil,
        encodeWords, List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero,
        List.replicate_zero, NormalizationStream.blocks, List.reverse_nil] using
        emptyStep tape distinct labels done rejected program atLabels base ambient suffix
          freshBase clauseCounter output
  | cons clause clauses ih =>
      have first := bodyTrace tape distinct labels done rejected program atLabels base ambient
        clause (encodeWords (clauses.flatMap clauseWords) ++ suffix) freshBase clauses.length
        clauseCounter output empty
      have rest := ih (freshBase + 4) (List.replicate 13 true ++ clauseCounter)
        ((bits (clauseSigns clause) (clauseNames clause) freshBase).reverse ++ output)
      have full := joinTrace first rest
      have freshEq : freshBase + 4 + 4 * clauses.length =
          freshBase + 4 * (clauses.length + 1) := by omega
      have countEq : List.replicate (13 * clauses.length) true ++
          (List.replicate 13 true ++ clauseCounter) =
          List.replicate (13 * (clauses.length + 1)) true ++ clauseCounter := by
        rw [Nat.mul_add, Nat.mul_one, List.replicate_add, List.append_assoc]
      simpa only [steps, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons, freshEq, countEq, NormalizationStream.blocks,
        List.reverse_append] using full

def loopInTime {n : Nat} (clauses : List (Target.Clause n)) (suffix : List Bool)
    (freshBase maximum : Nat) (clauseCounter output : List Bool)
    (empty : ∀ i : Fin 9, 4 ≤ i.val → i.val ≤ 7 → base (tape i) = [])
    (nameBound : n ≤ maximum) (freshBound : freshBase + 4 * clauses.length ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .guard), reset ambient,
        loopTapes tape base (encodeWords (clauses.flatMap clauseWords) ++ suffix)
          freshBase clauses.length clauseCounter output⟩
      (some ⟨done, reset ambient,
        loopTapes tape base suffix (freshBase + 4 * clauses.length) 0
          (List.replicate (13 * clauses.length) true ++ clauseCounter)
          ((NormalizationStream.blocks freshBase clauses).reverse ++ output)⟩)
      (clauses.length * (84 * maximum + 128) + 1) where
  steps := steps freshBase clauses
  evals_in_steps := loopTrace tape distinct labels done rejected program atLabels base ambient
    clauses suffix freshBase clauseCounter output empty
  steps_le_m := steps_le freshBase maximum clauses nameBound freshBound

end BinPackingCompleteness.NormalizationLoopMachine

end OAI
