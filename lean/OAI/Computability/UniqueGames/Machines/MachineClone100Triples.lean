import Mathlib.Data.List.TakeDrop
import OAI.Computability.UniqueGames.Machines.MachineClone100TableLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Triples

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model MachineClone100Context MachineClone100Affine

def rowOutput (t : Nat × Nat × Nat) (base : Tape → List Bool) : List Bool :=
  (base (.field 0)).flatMap (affineEmit 100 t.1) ++
    (base (.field 1)).flatMap (affineEmit 100 t.2.1) ++
    (base (.field 2)).flatMap (affineEmit 100 t.2.2) ++
    (base (.field 3)).flatMap (affineEmit 1 0)

def rowSteps (base : Tape → List Bool) : Nat :=
  3 * ((base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length) + 12

def startAt (D i : Nat) : Option (Label D) :=
  if h : i < D then some (.setup (.inr (⟨i, h⟩, 0))) else some (.cleanup 0)

@[simp] theorem contextTapes_field (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (base : Tape → List Bool) (j : Fin 4) :
    contextTapes triples c base (.field j) = base (.field j) :=
  contextTapes_other triples c base _ (by intro h; cases h)

@[simp] theorem rowOutput_update (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (out : List Bool) :
    rowOutput t (Function.update base .reversed out) = rowOutput t base := by
  simp [rowOutput]

@[simp] theorem rowSteps_update (base : Tape → List Bool) (out : List Bool) :
    rowSteps (Function.update base .reversed out) = rowSteps base := by
  simp [rowSteps]

private theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

theorem fourContexts_tapes (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (base : Tape → List Bool) :
    contextTapes triples (.inr (i, 3))
      (contextTapes triples (.inr (i, 2))
        (contextTapes triples (.inr (i, 1))
          (contextTapes triples (.inr (i, 0)) base))) =
      Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
        base .reversed) := by
  simp [contextTapes, output_eq_flatMap, emission, contextSource, contextScale,
    contextOffset, tripleField, rowOutput, List.reverse_append, List.append_assoc]

/-- Execute each of the four actual contexts in slot order. -/
theorem rowTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (i : Fin triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[rowSteps base]
      (some ⟨some (.setup (.inr (i, 0))), state, base⟩) =
      some ⟨startAt triples.length (i.val + 1), initialState _,
        Function.update base .reversed ((rowOutput (triples.get i) base).reverse ++
          base .reversed)⟩ := by
  let b1 := contextTapes triples (.inr (i, 0)) base
  let b2 := contextTapes triples (.inr (i, 1)) b1
  let b3 := contextTapes triples (.inr (i, 2)) b2
  have h0 := contextTrace triples nonempty (.inr (i, 0)) base scratchEmpty state
  have h1 := contextTrace triples nonempty (.inr (i, 1)) b1
    (by simpa [b1] using scratchEmpty) (initialState _)
  have h2 := contextTrace triples nonempty (.inr (i, 2)) b2
    (by simpa [b2, b1] using scratchEmpty) (initialState _)
  have h3 := contextTrace triples nonempty (.inr (i, 3)) b3
    (by simpa [b3, b2, b1] using scratchEmpty) (initialState _)
  have next0 : contextNext (.inr (i, (0 : Fin 4))) = some (.setup (.inr (i, 1))) := rfl
  have next1 : contextNext (.inr (i, (1 : Fin 4))) = some (.setup (.inr (i, 2))) := rfl
  have next2 : contextNext (.inr (i, (2 : Fin 4))) = some (.setup (.inr (i, 3))) := rfl
  have next3 : contextNext (.inr (i, (3 : Fin 4))) =
      startAt triples.length (i.val + 1) := by simp [contextNext, startAt]
  rw [next0] at h0
  rw [next1] at h1
  rw [next2] at h2
  rw [next3] at h3
  have combined := chain (chain (chain h0 h1) h2) h3
  simp only [contextSource, b3, b2, b1, contextTapes_field] at combined
  rw [fourContexts_tapes] at combined
  convert combined using 1
  unfold rowSteps
  congr 1
  omega

private theorem tailTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (remaining : Nat) :
    ∀ (i : Nat), i + remaining = triples.length →
      ∀ (base : Tape → List Bool) (_scratchEmpty : base .scratch = [])
        (state : State triples.length),
        (remaining = 0 → state = initialState _) →
        (MachineComposition.advance (TM2.step (program triples nonempty)))^[remaining * rowSteps base]
          (some ⟨startAt triples.length i, state, base⟩) =
          some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
            (((triples.drop i).flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  induction remaining with
  | zero =>
      intro i hi base scratchEmpty state finalState
      have heq : i = triples.length := by omega
      subst i
      rw [finalState rfl]
      simp [startAt]
  | succ remaining ih =>
      intro i hi base scratchEmpty state finalState
      have hiLt : i < triples.length := by omega
      let index : Fin triples.length := ⟨i, hiLt⟩
      let after := Function.update base .reversed
        ((rowOutput (triples.get index) base).reverse ++ base .reversed)
      have row := rowTrace triples nonempty index base scratchEmpty state
      have rest := ih (i + 1) (by omega) after
        (by simpa [after] using scratchEmpty) (initialState _) (by intro _; rfl)
      have combined := chain row rest
      have dropHead : triples.drop i = triples.get index :: triples.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt triples.length i = some (.setup (.inr (index, 0))) := by
        simp [startAt, hiLt, index]
      rw [hstart]
      simp only [after, rowSteps_update, rowOutput_update] at combined
      simp only [Function.update_self, Function.update_idem] at combined
      rw [dropHead]
      simp only [List.flatMap_cons, List.reverse_append, List.append_assoc]
      convert combined using 1
      congr 1
      simp [Nat.add_mul]

theorem tableTrace_raw (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[triples.length * rowSteps base]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((triples.flatMap (fun t => rowOutput t base)).reverse ++ base .reversed)⟩ := by
  have h := tailTrace triples nonempty triples.length 0 (by omega) base scratchEmpty state
    (by intro hz; exact False.elim (by have := List.length_pos_iff.mpr nonempty; omega))
  simpa [startAt, List.length_pos_iff.mpr nonempty] using h

def affineRecord (a b c rhs : Nat) (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * a, t.2.1 + 100 * b, t.2.2 + 100 * c, rhs]

theorem rowOutput_words (t : Nat × Nat × Nat) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    rowOutput t base = encodeWords (affineRecord a b c rhs t) := by
  simp [rowOutput, h0, h1, h2, h3, affineEmit_word, affineRecord, encodeWords,
    List.append_assoc]

theorem tableOutput_words (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    triples.flatMap (fun t => rowOutput t base) =
      encodeWords (triples.flatMap (affineRecord a b c rhs)) := by
  induction triples with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.flatMap_cons, encodeWords_append, ih,
        rowOutput_words t base a b c rhs h0 h1 h2 h3]

/-- The actual inner loop outputs the concrete cloned equation words. -/
theorem tableTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (scratchEmpty : base .scratch = [])
    (state : State triples.length) (a b c rhs : Nat)
    (h0 : base (.field 0) = encodeWord a) (h1 : base (.field 1) = encodeWord b)
    (h2 : base (.field 2) = encodeWord c) (h3 : base (.field 3) = encodeWord rhs) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      triples.length * (3 * ((a + 1) + (b + 1) + (c + 1) + (rhs + 1)) + 12)]
      (some ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), state, base⟩) =
      some ⟨some (.cleanup 0), initialState _, Function.update base .reversed
        ((encodeWords (triples.flatMap (affineRecord a b c rhs))).reverse ++ base .reversed)⟩ := by
  have h := tableTrace_raw triples nonempty base scratchEmpty state
  rw [tableOutput_words triples base a b c rhs h0 h1 h2 h3] at h
  simpa only [rowSteps, h0, h1, h2, h3, encodeWord_length] using h

theorem tableTapes_other (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (tape : Tape) (different : tape ≠ .reversed) :
    Function.update base .reversed
      ((triples.flatMap (fun t => rowOutput t base)).reverse ++ base .reversed) tape =
      base tape := by simp [different]

end UniqueGamesTheorem.Explicit.MachineClone100Triples

end

end OAI
