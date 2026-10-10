import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineFiniteTable

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

def inputTapes (bits : List Bool) : Tape → List Bool
  | .input => bits
  | _ => []

private def firstTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => encodeWord m ++ clauseBits
  | .«variables» => encodeWord n
  | _ => []

def counterTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | _ => []

private def headerTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

def startTapes (n m : ℕ) (clauseBits : List Bool) : Tape → List Bool
  | .input => clauseBits
  | .«variables» => encodeWord n
  | .counter => encodeWord m
  | .index => [false]
  | .reversed => (encodeWords [n + m + 1, 6 * m + 1]).reverse
  | _ => []

theorem initList_eq (bits : List Bool) :
    initList machine bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  cases k <;> rfl

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem readCountersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[n + m + 4]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩ := by
  let t0 := inputTapes (encodeWords [n, m] ++ clauseBits)
  have first := (SourceMachine.fieldInTime .input .«variables» (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    t0 n (encodeWord m ++ clauseBits)
    (by simp [t0, inputTapes, encodeWords, List.append_assoc])
    (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, t0⟩) = _ at first
  have firstFrame : SourceMachine.fieldTapes .input .«variables» t0
      (encodeWord m ++ clauseBits) (encodeWord n ++ t0 .«variables») =
      firstTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, t0, inputTapes, firstTapes]
  rw [firstFrame] at first
  have second := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some .scanN) program rfl rfl
    (firstTapes n m clauseBits) m clauseBits rfl (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, firstTapes n m clauseBits⟩) = _ at second
  have secondFrame : SourceMachine.fieldTapes .input .counter (firstTapes n m clauseBits)
      clauseBits (encodeWord m ++ firstTapes n m clauseBits .counter) =
      counterTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, firstTapes, counterTapes]
  rw [secondFrame] at second
  have total := trace_trans _ first second
  rw [show (n + 2) + (m + 2) = n + m + 4 by omega] at total
  rw [initList_eq]
  exact total

theorem headersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩) =
      some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩ := by
  have h := MachineInitialHeaders.headerTrace .«variables» .counter .scratch .reversed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    .scanN .restoreN .scanM1 .restoreM1 .closeFirst .scanM6 .restoreM6 .closeSecond
    (some .initializeIndex) program rfl rfl rfl rfl rfl rfl rfl rfl
    (counterTapes n m clauseBits) n m [] []
    (by simp [counterTapes]) (by simp [counterTapes]) rfl
    (false, false, false) none
  have frame : Function.update (counterTapes n m clauseBits) .reversed
      ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++
        counterTapes n m clauseBits .reversed) = headerTapes n m clauseBits := by
    funext k
    cases k <;> simp [counterTapes, headerTapes]
  rw [frame] at h
  exact h

theorem initializeIndexTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .initializeIndex, initialState, headerTapes n m clauseBits⟩) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program .initializeIndex) initialState
    (headerTapes n m clauseBits)) = _
  simp only [program, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [headerTapes, startTapes]

theorem startTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * n + 5 * m + 13]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  have total := trace_trans _
    (trace_trans _ (readCountersTrace n m clauseBits) (headersTrace n m clauseBits))
    (initializeIndexTrace n m clauseBits)
  simpa only [show (n + m + 4) + (2 * n + 4 * m + 8) + 1 =
    3 * n + 5 * m + 13 by omega] using total

theorem formulaStartTrace (F : Target.Formula) :
    (MachineComposition.advance (TM2.step program))^[
        3 * F.«variables» + 5 * F.clauses.length + 13]
      (some (initList machine (formulaBits F))) =
      some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩ := by
  simpa only [formulaBits, formulaWords, encodeWords_append] using
    startTrace F.«variables» F.clauses.length (encodeWords (F.clauses.flatMap clauseWords))

def startInTime (n m : ℕ) (clauseBits : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (initList machine (encodeWords [n, m] ++ clauseBits))
      (some ⟨some .guard, initialState, startTapes n m clauseBits⟩)
      (3 * n + 5 * m + 13) where
  steps := 3 * n + 5 * m + 13
  evals_in_steps := startTrace n m clauseBits
  steps_le_m := Nat.le_refl _

def formulaStartInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step program) (initList machine (formulaBits F))
      (some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩)
      (3 * F.«variables» + 5 * F.clauses.length + 13) where
  steps := 3 * F.«variables» + 5 * F.clauses.length + 13
  evals_in_steps := formulaStartTrace F
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.PCP.RawInitialMachineStart

end OAI
