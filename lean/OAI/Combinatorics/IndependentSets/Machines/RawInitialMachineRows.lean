import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineLoopData

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

attribute [local irreducible] relationOutput RawInitialRows.relationWordsFor

abbrev advance := MachineComposition.advance (TM2.step program)

def outputTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update base .reversed (bits ++ base .reversed)

@[simp] theorem outputTapes_reversed (base : Tape → List Bool) (bits : List Bool) :
    outputTapes base bits .reversed = bits ++ base .reversed := by simp [outputTapes]

theorem outputTapes_other (base : Tape → List Bool) (bits : List Bool)
    (tape : Tape) (h : tape ≠ .reversed) : outputTapes base bits tape = base tape := by
  simp [outputTapes, h]

@[simp] theorem outputTapes_twice (base : Tape → List Bool) (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  funext tape
  by_cases h : tape = .reversed
  · subst tape; simp [List.append_assoc]
  · simp [outputTapes, h]

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

private theorem copyTrace (phase : CopyPhase) (base : Tape → List Bool)
    (n : ℕ) (hsource : base (copySource phase) = encodeWord n)
    (hscratch : base .scratch = []) (signs : Signs) :
    advance^[2 * n + 2] (some ⟨some (.scan phase), (signs, none), base⟩) =
      some ⟨some (copyNext phase), (signs, none),
        outputTapes base (List.replicate (copyScale phase * n) true)⟩ :=
  (copyInTime phase base n [] (by simpa using hsource) hscratch (signs, none)).evals_in_steps

private theorem closeTailTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none),
        outputTapes base [false]⟩ := by
  change some (TM2.stepAux (program (.closeTail slot orientation)) (signs, none) base) = _
  rfl

private theorem closeReverseTrace (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance^[1] (some ⟨some (.closeReverse slot orientation), (signs, none), base⟩) =
      some ⟨some (.relation slot orientation), (signs, none),
        outputTapes base (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed
    (encodeWord (2 * slot.val + if orientation then 0 else 1))
    (.closeReverse slot orientation) (some (.relation slot orientation))
    program rfl base signs none

private theorem reverse_encodeWord_add (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

def rowEndBits (slot : Fin 3) (orientation : Bool) (i : ℕ) (signs : Signs) : List Bool :=
  relationOutput slot orientation (signs, none) ++
    (encodeWord (6 * i + 2 * slot.val + if orientation then 0 else 1)).reverse ++ [false]

private theorem rowEndTrace (slot : Fin 3) (orientation : Bool) (base : Tape → List Bool)
    (i : ℕ) (hindex : base .index = encodeWord i) (hscratch : base .scratch = [])
    (signs : Signs) :
    advance^[2 * i + 5] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (relationNext slot orientation), (signs, none),
        outputTapes base (rowEndBits slot orientation i signs)⟩ := by
  let first := outputTapes base [false]
  let second := outputTapes first (List.replicate (6 * i) true)
  let third := outputTapes second
    (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse
  have h1 := closeTailTrace slot orientation base signs
  have h2 := copyTrace (.reverseIndex slot orientation) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none), first⟩) =
    some ⟨some (.closeReverse slot orientation), (signs, none), second⟩ at h2
  have h3 := closeReverseTrace slot orientation second signs
  have h4 := (relationInTime slot orientation third (signs, none)).evals_in_steps
  change advance^[1] (some ⟨some (.relation slot orientation), (signs, none), third⟩) =
    some ⟨some (relationNext slot orientation), (signs, none),
      outputTapes third (relationOutput slot orientation (signs, none))⟩ at h4
  have total := trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) h4
  have hout : outputTapes third (relationOutput slot orientation (signs, none)) =
      outputTapes base (rowEndBits slot orientation i signs) := by
    simp only [third, second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [reverse_encodeWord_add]
    simp only [rowEndBits, Nat.add_assoc, List.append_assoc]
  rw [hout] at total
  simpa only [show 1 + (2 * i + 2) + 1 + 1 = 2 * i + 5 by omega] using total

private theorem rowEndBits_append (slot : Fin 3) (orientation : Bool)
    (tail i : ℕ) (signs : Signs) :
    rowEndBits slot orientation i signs ++ List.replicate tail true =
      (encodeWords ([tail, 6 * i + 2 * slot.val + if orientation then 0 else 1] ++
        RawInitialRows.relationWordsFor signs (RawInitialTables.slotOrder.symm slot) orientation)).reverse := by
  simp only [rowEndBits, relationOutput, encodeWords_append, encodeWords,
    List.append_nil, List.reverse_append, encodeWord,
    List.reverse_replicate, List.reverse_singleton, List.append_assoc]

theorem falseRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hscratch : base .scratch = []) :
    advance^[2 * n + 4 * i + 9]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (.scan (.variableName slot)), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) false)).reverse⟩ := by
  let first := outputTapes base (List.replicate n true)
  let second := outputTapes first (List.replicate i true)
  have h1 := copyTrace (.tailVariables slot) base n hvariables hscratch signs
  have h2 := copyTrace (.tailIndex slot) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1 h2
  change advance^[2 * n + 2]
    (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩ at h1
  change advance^[2 * i + 2]
    (some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩) =
    some ⟨some (.closeTail slot false), (signs, none), second⟩ at h2
  have h3 := rowEndTrace slot false second i
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes] using hscratch) signs
  have total := trace_trans _ (trace_trans _ h1 h2) h3
  have hout : outputTapes second (rowEndBits slot false i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) false)).reverse := by
    simp only [second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [← List.replicate_add, Nat.add_comm i n, rowEndBits_append]
    simp only [RawInitialRows.incidenceWords, Bool.false_eq_true, ↓reduceIte,
      Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [relationNext, Bool.false_eq_true, ↓reduceIte,
    show (2 * n + 2) + (2 * i + 2) + (2 * i + 5) = 2 * n + 4 * i + 9 by omega] using total

theorem trueRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hindex : base .index = encodeWord i) (hscratch : base .scratch = []) :
    advance^[2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7]
      (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) true)).reverse⟩ := by
  let value := RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)
  let first := outputTapes base (List.replicate value true)
  have h1 := copyTrace (.variableName slot) base value hname hscratch signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1
  change advance^[2 * value + 2]
    (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
    some ⟨some (.closeTail slot true), (signs, none), first⟩ at h1
  have h2 := rowEndTrace slot true first i
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  have total := trace_trans _ h1 h2
  have hout : outputTapes first (rowEndBits slot true i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) true)).reverse := by
    simp only [first, outputTapes_twice, rowEndBits_append, value,
      RawInitialRows.incidenceWords, ↓reduceIte, Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [value, show (2 * value + 2) + (2 * i + 5) = 2 * value + 2 * i + 7 by omega] using total

def pairWords (slot : Fin 3) (n i : ℕ) (names : RawInitialRows.Names)
    (signs : Signs) : List ℕ :=
  RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) false ++
    RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) true

theorem pairTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hscratch : base .scratch = []) :
    advance^[2 * n + 6 * i +
      2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (pairWords slot n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
    (RawInitialTables.slotOrder.symm slot) false)).reverse
  have h1 := falseRowTrace slot base n i names signs hvariables hindex hscratch
  have h2 := trueRowTrace slot first n i names signs
    (by simpa [first, outputTapes] using hname)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch)
  have total := trace_trans _ h1 h2
  simpa only [first, outputTapes_twice, pairWords, encodeWords_append, List.reverse_append,
    show (2 * n + 4 * i + 9) +
      (2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7) =
      2 * n + 6 * i +
        2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16 by omega]
    using total

theorem rowsTrace (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    advance^[6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48]
      (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
      some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (pairWords 0 n i names signs)).reverse
  let second := outputTapes first (encodeWords (pairWords 1 n i names signs)).reverse
  have h0 := pairTrace 0 base n i names signs hvariables hindex hname0 hscratch
  have h1 := pairTrace 1 first n i names signs
    (by simpa [first, outputTapes] using hvariables)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname2)
    (by simpa [first, outputTapes] using hscratch)
  have h2 := pairTrace 2 second n i names signs
    (by simpa [second, first, outputTapes] using hvariables)
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname4)
    (by simpa [second, first, outputTapes] using hscratch)
  change advance^[2 * n + 6 * i + 2 * names.1 + 16]
    (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩ at h0
  change advance^[2 * n + 6 * i + 2 * names.2.1 + 16]
    (some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩) =
    some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩ at h1
  change advance^[2 * n + 6 * i + 2 * names.2.2 + 16]
    (some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩) =
    some ⟨some (.cleanupField 0), (signs, none),
      outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse⟩ at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
  have hout : outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse =
      outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse := by
    simp only [second, first, outputTapes_twice, RawInitialRows.clauseWords,
      encodeWords_append, List.reverse_append, pairWords, List.append_assoc]
    rfl
  rw [hout] at total
  simpa only [show (2 * n + 6 * i + 2 * names.1 + 16) +
    (2 * n + 6 * i + 2 * names.2.1 + 16) + (2 * n + 6 * i + 2 * names.2.2 + 16) =
      6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48 by omega] using total

def rowsInTime (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩
      (some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩)
      (6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48) where
  steps := 6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48
  evals_in_steps := rowsTrace base n i names signs hvariables hindex hname0 hname2 hname4 hscratch
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.PCP.RawInitialMachineRows

end OAI
