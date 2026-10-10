import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.Clone100Counting

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Explicit.MachineClone100Affine

open DFVSGames.Reduction

open DFVSGames.Foundations.Complexity
open MachineClone100Model

theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem output_append {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (first rest : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q (first ++ rest) =
      MachineTransducer.output (fun state _ => state) emit q first ++
        MachineTransducer.output (fun state _ => state) emit q rest := by
  simp only [output_eq_flatMap, List.flatMap_append]

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

theorem affineEmit_word_append (scale offset v : Nat) (rest : List Bool) :
    (encodeWord v ++ rest).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) ++ rest.flatMap (affineEmit scale offset) := by
  rw [List.flatMap_append, affineEmit_word]

theorem affineEmit_words (scale offset : Nat) (vs : List Nat) :
    (encodeWords vs).flatMap (affineEmit scale offset) =
      encodeWords (vs.map (fun v => offset + scale * v)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [encodeWords, List.flatMap_append, List.map_cons, affineEmit_word, ih]

theorem output_word (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v) =
      encodeWord (contextOffset triples c + contextScale c * v) := by
  rw [output_eq_flatMap]
  exact affineEmit_word (contextScale c) (contextOffset triples c) v

theorem output_word_append (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) (rest : List Bool) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v ++ rest) =
      encodeWord (contextOffset triples c + contextScale c * v) ++
        MachineTransducer.output (fun q _ => q) (emission triples) c rest := by
  rw [output_append, output_word]

theorem output_words (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (vs : List Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWords vs) =
      encodeWords (vs.map (fun v => contextOffset triples c + contextScale c * v)) := by
  rw [output_eq_flatMap]
  exact affineEmit_words (contextScale c) (contextOffset triples c) vs

theorem output_header_variables (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 0) (encodeWord v) =
      encodeWord (100 * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 0) v

theorem output_header_count (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 1) (encodeWord v) =
      encodeWord (triples.length * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 1) v

theorem output_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (j : Fin 4) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, j)) (encodeWord v) =
      encodeWord (tripleField (triples.get i) j + (if j.val < 3 then 100 else 1) * v) := by
  exact output_word triples (.inr (i, j)) v

theorem output_first_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 0)) (encodeWord v) =
      encodeWord ((triples.get i).1 + 100 * v) := by
  simpa [tripleField] using output_field triples i 0 v

theorem output_second_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 1)) (encodeWord v) =
      encodeWord ((triples.get i).2.1 + 100 * v) := by
  simpa [tripleField] using output_field triples i 1 v

theorem output_third_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 2)) (encodeWord v) =
      encodeWord ((triples.get i).2.2 + 100 * v) := by
  simpa [tripleField] using output_field triples i 2 v

theorem output_rhs_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 3)) (encodeWord v) =
      encodeWord v := by
  simpa [tripleField] using output_field triples i 3 v

end DFVSGames.Explicit.MachineClone100Affine
end

section

namespace DFVSGames.Explicit.MachineClone100Cleanup

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

variable {D : Nat}

theorem drainStep_cons (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (bit : Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape (bit :: input)⟩ =
      some ⟨some again, (control, some bit), Function.update base tape input⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape (bit :: input))) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainStep_nil (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape []⟩ =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape [])) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainTrace (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (input : List Bool)
    (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (control, register), Function.update base tape input⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  induction input generalizing register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some] using
      drainStep_nil tape again next program atAgain base control register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some again, (control, register),
        Function.update base tape (bit :: input)⟩) = _
    rw [drainStep_cons tape again next program atAgain, ih]

theorem drainTrace_base (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(base tape).length + 1]
      (some ⟨some again, (control, register), base⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self] using
    drainTrace tape again next program atAgain base (base tape) control register

def drainInTime (tape : Tape) (again next : Label D)
    (program : Label D → TM2.Stmt Alphabet (Label D) (State D))
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context D) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (control, register), base⟩
      (some ⟨some next, (control, none), Function.update base tape []⟩)
      ((base tape).length + 1) where
  steps := (base tape).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[_] _ = _
    exact drainTrace_base tape again next program atAgain base control register
  steps_le_m := Nat.le_refl _

theorem clearHeaderTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[(base .header).length + 1]
      (some ⟨some .clearHeader, (control, register), base⟩) =
      some ⟨some .guard, (control, none), Function.update base .header []⟩ :=
  drainTrace_base .header .clearHeader .guard (program triples nonempty) rfl base control register

def clearHeaderInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .clearHeader, (control, register), base⟩
      (some ⟨some .guard, (control, none), Function.update base .header []⟩)
      ((base .header).length + 1) :=
  drainInTime .header .clearHeader .guard (program triples nonempty) rfl base control register

def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]

theorem clearFields_other (base : Tape → List Bool) (tape : Tape)
    (other : ∀ j, tape ≠ .field j) : clearFields base tape = base tape := by
  simp [clearFields, other]

@[simp] theorem clearFields_input (base : Tape → List Bool) :
    clearFields base .input = base .input := by simp [clearFields]
@[simp] theorem clearFields_header (base : Tape → List Bool) :
    clearFields base .header = base .header := by simp [clearFields]
@[simp] theorem clearFields_counter (base : Tape → List Bool) :
    clearFields base .counter = base .counter := by simp [clearFields]
@[simp] theorem clearFields_scratch (base : Tape → List Bool) :
    clearFields base .scratch = base .scratch := by simp [clearFields]
@[simp] theorem clearFields_reversed (base : Tape → List Bool) :
    clearFields base .reversed = base .reversed := by simp [clearFields]
@[simp] theorem clearFields_output (base : Tape → List Bool) :
    clearFields base .output = base .output := by simp [clearFields]

theorem clearFields_eq_self (base : Tape → List Bool)
    (empty : ∀ j, base (.field j) = []) : clearFields base = base := by
  funext tape
  cases tape <;> simp [empty]

@[simp] theorem clearFields_idempotent (base : Tape → List Bool) :
    clearFields (clearFields base) = clearFields base :=
  clearFields_eq_self (clearFields base) (clearFields_field base)

def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

theorem cleanupTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (slot : Fin 4) (base : Tape → List Bool)
    (control : Unit × Context triples.length) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      (base (.field slot)).length + 1]
      (some ⟨some (.cleanup slot), (control, register), base⟩) =
      some ⟨some (cleanupNext slot), (control, none), Function.update base (.field slot) []⟩ :=
  drainTrace_base (.field slot) (.cleanup slot) (cleanupNext slot)
    (program triples nonempty) rfl base control register

theorem cleanupFourTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let t₀ := Function.update base (.field 0) []
  let t₁ := Function.update t₀ (.field 1) []
  let t₂ := Function.update t₁ (.field 2) []
  have h₀ := cleanupTrace triples nonempty 0 base control register
  have h₁ := cleanupTrace triples nonempty 1 t₀ control none
  have h₂ := cleanupTrace triples nonempty 2 t₁ control none
  have h₃ := cleanupTrace triples nonempty 3 t₂ control none
  have hn₀ : cleanupNext (D := triples.length) 0 = .cleanup 1 := by simp [cleanupNext]
  have hn₁ : cleanupNext (D := triples.length) 1 = .cleanup 2 := by simp [cleanupNext]
  have hn₂ : cleanupNext (D := triples.length) 2 = .cleanup 3 := by simp [cleanupNext]
  have hn₃ : cleanupNext (D := triples.length) 3 = .guard := by simp [cleanupNext]
  rw [hn₀] at h₀
  rw [hn₁] at h₁
  rw [hn₂] at h₂
  rw [hn₃] at h₃
  have ht₁ : t₀ (.field 1) = base (.field 1) := by simp [t₀]
  have ht₂ : t₁ (.field 2) = base (.field 2) := by simp [t₁, t₀]
  have ht₃ : t₂ (.field 3) = base (.field 3) := by simp [t₂, t₁, t₀]
  rw [ht₁] at h₁
  rw [ht₂] at h₂
  rw [ht₃] at h₃
  have time : cleanupSteps base =
      ((base (.field 3)).length + 1) +
      (((base (.field 2)).length + 1) +
      (((base (.field 1)).length + 1) + ((base (.field 0)).length + 1))) := by
    unfold cleanupSteps
    omega
  rw [time, Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base (.field 2)).length + 1)]
  rw [Function.iterate_add_apply (m := (base (.field 1)).length + 1)]
  rw [h₀, h₁, h₂, h₃]
  rfl

def cleanupFourInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
    exact cleanupFourTrace triples nonempty base control register
  steps_le_m := Nat.le_refl _

end DFVSGames.Explicit.MachineClone100Cleanup
end

section

namespace DFVSGames.Explicit.MachineClone100Headers

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineClone100Model

def parsedTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | tape => base tape

def resultTapes (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (n m : Nat) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .header => []
  | .counter => encodeWord m
  | .reversed => (encodeWords [100 * n, triples.length * m]).reverse
  | tape => base tape

@[simp] theorem resultTapes_input (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .input = suffix := rfl
@[simp] theorem resultTapes_header (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .header = [] := rfl
@[simp] theorem resultTapes_counter (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .counter = encodeWord m := rfl
@[simp] theorem resultTapes_reversed (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .reversed =
      (encodeWords [100 * n, triples.length * m]).reverse := rfl
@[simp] theorem resultTapes_scratch (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .scratch = base .scratch := rfl
@[simp] theorem resultTapes_field (triples) (base) (n m) (suffix) (j : Fin 4) :
    resultTapes triples base n m suffix (.field j) = base (.field j) := rfl
@[simp] theorem resultTapes_output (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .output = base .output := rfl

private theorem twoFieldsTapes_inline_MachineClone100Headers (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hheader : base .header = []) (hcounter : base .counter = []) :
    SourceMachine.afterField .input .counter
      (SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)) m suffix =
      parsedTapes base n m suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hheader, hcounter]

private theorem firstContextTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hreversed : base .reversed = []) :
    MachineClone100Context.contextTapes triples (.inl 0) (parsedTapes base n m suffix) =
      Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale, hreversed]

private theorem secondContextTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    MachineClone100Context.contextTapes triples (.inl 1)
      (Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse) =
      Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale,
    encodeWords, List.reverse_append]

private theorem clearHeaderTapes_inline_MachineClone100Headers (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse) .header [] =
      resultTapes triples base n m suffix := by
  funext tape
  cases tape <;> simp [parsedTapes, resultTapes]

theorem headersTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[5 * n + 4 * m + 18]
      (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
      some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩ := by
  let t₀ := SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)
  let t₁ := parsedTapes base n m suffix
  let t₂ := Function.update t₁ .reversed (encodeWord (100 * n)).reverse
  let t₃ := Function.update t₁ .reversed (encodeWords [100 * n, triples.length * m]).reverse
  have h₀ : base .input = encodeWord n ++ (encodeWord m ++ suffix) := by
    simpa only [encodeWords, List.append_nil, List.append_assoc] using hinput
  have p₀ := (SourceMachine.fieldInTime .input .header (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1))
    (program triples hne) rfl rfl base n (encodeWord m ++ suffix) h₀
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[n + 2]
    (some ⟨some (.headerStart 0), initialState triples.length, base⟩) =
    some ⟨some (.headerStart 1), initialState triples.length, t₀⟩ at p₀
  have h₁ : t₀ .input = encodeWord m ++ suffix := by
    simp [t₀, SourceMachine.afterField]
  have p₁ := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some (.setup (.inl 0)))
    (program triples hne) rfl rfl t₀ m suffix h₁
    ((), defaultControl triples.length) none).evals_in_steps
  change (MachineComposition.advance (TM2.step (program triples hne)))^[m + 2]
    (some ⟨some (.headerStart 1), initialState triples.length, t₀⟩) =
    some ⟨some (.setup (.inl 0)), initialState triples.length,
      SourceMachine.afterField .input .counter t₀ m suffix⟩ at p₁
  have ht₁ : SourceMachine.afterField .input .counter t₀ m suffix = t₁ :=
    twoFieldsTapes_inline_MachineClone100Headers base n m suffix hheader hcounter
  rw [ht₁] at p₁
  have hs₁ : t₁ .scratch = [] := by simpa [t₁, parsedTapes] using hscratch
  have p₂ := MachineClone100Context.contextTrace triples hne (.inl 0) t₁ hs₁
    (initialState triples.length)
  have ht₂ : MachineClone100Context.contextTapes triples (.inl 0) t₁ = t₂ :=
    firstContextTapes_inline_MachineClone100Headers triples base n m suffix hreversed
  rw [ht₂] at p₂
  have hlen₂ : (t₁ (contextSource (.inl 0 : Context triples.length))).length = n + 1 := by
    simp [contextSource, headerTape, t₁, parsedTapes]
  rw [hlen₂] at p₂
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (n + 1) + 3]
    (some ⟨some (.setup (.inl 0)), initialState triples.length, t₁⟩) =
    some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩ at p₂
  have hs₂ : t₂ .scratch = [] := by simp [t₂, t₁, parsedTapes, hscratch]
  have p₃ := MachineClone100Context.contextTrace triples hne (.inl 1) t₂ hs₂
    (initialState triples.length)
  have ht₃ : MachineClone100Context.contextTapes triples (.inl 1) t₂ = t₃ :=
    secondContextTapes_inline_MachineClone100Headers triples base n m suffix
  rw [ht₃] at p₃
  have hlen₃ : (t₂ (contextSource (.inl 1 : Context triples.length))).length = m + 1 := by
    simp [contextSource, headerTape, t₂, t₁, parsedTapes]
  rw [hlen₃] at p₃
  change (MachineComposition.advance (TM2.step (program triples hne)))^[3 * (m + 1) + 3]
    (some ⟨some (.setup (.inl 1)), initialState triples.length, t₂⟩) =
    some ⟨some .clearHeader, initialState triples.length, t₃⟩ at p₃
  have p₄ := MachineClone100Cleanup.clearHeaderTrace triples hne t₃
    ((), defaultControl triples.length) none
  have ht₄ : Function.update t₃ .header [] = resultTapes triples base n m suffix :=
    clearHeaderTapes_inline_MachineClone100Headers triples base n m suffix
  rw [ht₄] at p₄
  have hh₃ : t₃ .header = encodeWord n := by simp [t₃, t₁, parsedTapes]
  rw [hh₃, encodeWord_length] at p₄
  change (MachineComposition.advance (TM2.step (program triples hne)))^[(n + 1) + 1]
    (some ⟨some .clearHeader, initialState triples.length, t₃⟩) =
    some ⟨some .guard, initialState triples.length, resultTapes triples base n m suffix⟩ at p₄
  rw [show 5 * n + 4 * m + 18 =
      (n + 2) + (3 * (m + 1) + 3) + (3 * (n + 1) + 3) + (m + 2) + (n + 2) by omega,
    Function.iterate_add_apply, p₀, Function.iterate_add_apply, p₁,
    Function.iterate_add_apply, p₂, Function.iterate_add_apply, p₃]
  exact p₄

def headersInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m] ++ suffix)
    (hheader : base .header = []) (hcounter : base .counter = [])
    (hscratch : base .scratch = []) (hreversed : base .reversed = []) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some (.headerStart 0), initialState triples.length, base⟩
      (some ⟨some .guard, initialState triples.length,
        resultTapes triples base n m suffix⟩) (5 * n + 4 * m + 18) where
  steps := 5 * n + 4 * m + 18
  evals_in_steps := headersTrace triples hne base n m suffix hinput hheader hcounter hscratch hreversed
  steps_le_m := Nat.le_refl _

theorem headersTime_linear (n m : Nat) : 5 * n + 4 * m + 18 ≤ 5 * (n + m) + 18 := by omega

end DFVSGames.Explicit.MachineClone100Headers
end

section

namespace DFVSGames.Explicit.MachineClone100Triples

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
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

private theorem chain_inline_MachineClone100Triples {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
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
  have combined := chain_inline_MachineClone100Triples (chain_inline_MachineClone100Triples (chain_inline_MachineClone100Triples h0 h1) h2) h3
  simp only [contextSource, b3, b2, b1, contextTapes_field] at combined
  rw [fourContexts_tapes] at combined
  convert combined using 1
  unfold rowSteps
  congr 1
  omega

private theorem tailTrace_inline_MachineClone100Triples (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
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
      have combined := chain_inline_MachineClone100Triples row rest
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
  have h := tailTrace_inline_MachineClone100Triples triples nonempty triples.length 0 (by omega) base scratchEmpty state
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

end DFVSGames.Explicit.MachineClone100Triples
end

section

namespace DFVSGames.Explicit.MachineClone100Loop

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineClone100Model

structure Record where
  a : Nat
  b : Nat
  c : Nat
  rhs : Nat

def recordWords (r : Record) : List Nat := [r.a, r.b, r.c, r.rhs]
def recordBits (r : Record) : List Bool := encodeWords (recordWords r)
def recordsBits (rs : List Record) : List Bool := rs.flatMap recordBits

def clonedRecordBits (triples : List (Nat × Nat × Nat)) (r : Record) : List Bool :=
  encodeWords (triples.flatMap (MachineClone100Triples.affineRecord r.a r.b r.c r.rhs))

def clonedRecordsBits (triples : List (Nat × Nat × Nat)) (rs : List Record) : List Bool :=
  rs.flatMap (clonedRecordBits triples)

def recordFields (r : Record) (j : Fin 4) : List Bool :=
  encodeWord (match j.val with | 0 => r.a | 1 => r.b | 2 => r.c | _ => r.rhs)

def tapes (base : Tape → List Bool) (input counter accumulator : List Bool)
    (fields : Fin 4 → List Bool) : Tape → List Bool
  | .input => input
  | .header => base .header
  | .counter => counter
  | .field j => fields j
  | .scratch => []
  | .reversed => accumulator
  | .output => base .output

theorem update_reversed (base : Tape → List Bool) (input counter acc out : List Bool)
    (fields : Fin 4 → List Bool) :
    Function.update (tapes base input counter acc fields) .reversed out =
      tapes base input counter out fields := by
  funext tape
  cases tape <;> simp [tapes]

theorem counterTapes_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes .counter
      (tapes base input counter acc fields) n [] =
      tapes base input (encodeWord n) acc fields := by
  funext tape
  cases tape <;> simp [MachineUnaryCounter.counterTapes, tapes]

theorem fourTapes_eq (base : Tape → List Bool) (input counter acc suffix : List Bool)
    (r : Record) :
    SourceMachine.fourTapes .input Tape.field
      (tapes base input counter acc (fun _ => [])) r.a r.b r.c r.rhs suffix =
      tapes base suffix counter acc (recordFields r) := by
  funext tape
  cases tape with
  | field j =>
    fin_cases j <;>
      simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
        tapes, recordFields]
  | _ =>
    simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
      tapes]

theorem clearFields_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (fields : Fin 4 → List Bool) :
    MachineClone100Cleanup.clearFields (tapes base input counter acc fields) =
      tapes base input counter acc (fun _ => []) := by
  funext tape
  cases tape <;> simp [tapes]

theorem cleanupSteps_eq (base : Tape → List Bool) (input counter acc : List Bool)
    (r : Record) :
    MachineClone100Cleanup.cleanupSteps (tapes base input counter acc (recordFields r)) =
      r.a + r.b + r.c + r.rhs + 8 := by
  simp [MachineClone100Cleanup.cleanupSteps, tapes, recordFields]
  omega

theorem recordBits_length (r : Record) :
    (recordBits r).length = r.a + r.b + r.c + r.rhs + 4 := by
  simp [recordBits, recordWords, encodeWords]
  omega

def bodyCost (D : Nat) (r : Record) : Nat :=
  (2 + 3 * D) * (recordBits r).length + (8 + 12 * D)

private theorem bodyCost_eq_inline_MachineClone100Loop (D : Nat) (r : Record) :
    ((r.a + r.b + r.c + r.rhs + 8) +
      D * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) +
      (r.a + r.b + r.c + r.rhs + 8) = bodyCost D r := by
  rw [bodyCost, recordBits_length]
  ring

def bodyInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (r : Record) (suffix counter acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.fieldStart 0), initialState _,
        tapes base (recordBits r ++ suffix) counter acc (fun _ => [])⟩
      (some ⟨some .guard, initialState _,
        tapes base suffix counter ((clonedRecordBits triples r).reverse ++ acc)
          (fun _ => [])⟩)
      (bodyCost triples.length r) := by
  let before := tapes base (recordBits r ++ suffix) counter acc (fun _ => [])
  let parsed := tapes base suffix counter acc (recordFields r)
  let out := (clonedRecordBits triples r).reverse ++ acc
  let emitted := tapes base suffix counter out (recordFields r)
  let parse := SourceMachine.fourFieldsInTime .input Tape.field
    (by intro j h; cases h) Label.fieldStart Label.fieldLoop
    (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))))
    (program triples nonempty) (by intro j; rfl) (by intro j; rfl)
    before r.a r.b r.c r.rhs suffix rfl ((), defaultControl _) none
  have parsed_eq : SourceMachine.fourTapes .input Tape.field before
      r.a r.b r.c r.rhs suffix = parsed := fourTapes_eq _ _ _ _ _ _
  rw [parsed_eq] at parse
  let table : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0))), initialState _, parsed⟩
      (some ⟨some (.cleanup 0), initialState _, emitted⟩)
      (triples.length * (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)) := {
    steps := triples.length *
      (3 * ((r.a + 1) + (r.b + 1) + (r.c + 1) + (r.rhs + 1)) + 12)
    evals_in_steps := by
      change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
      have h := MachineClone100Triples.tableTrace triples nonempty parsed rfl
        (initialState _) r.a r.b r.c r.rhs rfl rfl rfl rfl
      simpa only [parsed, tapes, update_reversed, clonedRecordBits, emitted, out] using h
    steps_le_m := Nat.le_refl _ }
  let cleanup := MachineClone100Cleanup.cleanupFourInTime triples nonempty emitted
    ((), defaultControl _) none
  have cleared : MachineClone100Cleanup.clearFields emitted =
      tapes base suffix counter out (fun _ => []) := clearFields_eq _ _ _ _ _
  rw [cleared] at cleanup
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parse table
  let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first cleanup
  exact {
    toEvalsTo := combined.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans combined.steps_le_m
      have hc : MachineClone100Cleanup.cleanupSteps emitted =
          r.a + r.b + r.c + r.rhs + 8 := cleanupSteps_eq _ _ _ _ _
      have hb := bodyCost_eq_inline_MachineClone100Loop triples.length r
      omega }

def loopCost (D : Nat) : List Record → Nat
  | [] => 1
  | r :: rs => (1 + bodyCost D r) + loopCost D rs

theorem loopCost_eq (D : Nat) (rs : List Record) :
    loopCost D rs = (2 + 3 * D) * (recordsBits rs).length +
      (9 + 12 * D) * rs.length + 1 := by
  induction rs with
  | nil => simp [loopCost, recordsBits]
  | cons r rs ih =>
    simp only [loopCost, ih, recordsBits, List.flatMap_cons, List.length_append,
      List.length_cons, bodyCost]
    ring

def loopInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      (loopCost triples.length rs) := by
  induction rs generalizing acc with
  | nil =>
    let guard := MachineUnaryCounter.guardInTime_zero .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl
      (tapes base suffix (encodeWord 0) acc (fun _ => [])) []
      ((), defaultControl _) none
    simpa only [counterTapes_eq, loopCost, recordsBits, clonedRecordsBits,
      List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
      initialState] using guard
  | cons r rs ih =>
    let before := tapes base (recordBits r ++ (recordsBits rs ++ suffix))
      (encodeWord (rs.length + 1)) acc (fun _ => [])
    let guard := MachineUnaryCounter.guardInTime_succ .counter Label.guard
      (.fieldStart 0) .finalCounter (program triples nonempty) rfl before rs.length []
      ((), defaultControl _) none
    simp only [before, counterTapes_eq] at guard
    let body := bodyInTime triples nonempty base r (recordsBits rs ++ suffix)
      (encodeWord rs.length) acc
    let rest := ih ((clonedRecordBits triples r).reverse ++ acc)
    let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    let combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [loopCost, recordsBits, clonedRecordsBits, List.flatMap_cons,
      List.length_cons, List.reverse_append, List.append_assoc, initialState,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

def loopInTime_linear (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (suffix : List Bool) (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _,
        tapes base (recordsBits rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _,
        tapes base suffix (encodeWord 0) ((clonedRecordsBits triples rs).reverse ++ acc)
          (fun _ => [])⟩)
      ((2 + 3 * triples.length) * (recordsBits rs).length +
        (9 + 12 * triples.length) * rs.length + 1) := by
  simpa only [loopCost_eq] using loopInTime triples nonempty base suffix rs acc

def recordOfEquation {n : Nat} (e : CloneGap.Equation (Fin n)) : Record :=
  ⟨e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0⟩

theorem recordsBits_equations {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    recordsBits (es.map recordOfEquation) =
      encodeWords (es.flatMap SourceEncoding.equationWords) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, recordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

theorem clonedRecordsBits_equations_table (triples : List (Nat × Nat × Nat))
    {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    clonedRecordsBits triples (es.map recordOfEquation) =
      encodeWords (es.flatMap fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, clonedRecordsBits, List.flatMap_cons, encodeWords_append] at *
    rw [ih]
    rfl

def sourceLoopInTime_table (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (base : Tape → List Bool) (suffix acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, tapes base
        (encodeWords (es.flatMap SourceEncoding.equationWords) ++ suffix)
        (encodeWord es.length) acc (fun _ => [])⟩
      (some ⟨some .finalCounter, initialState _, tapes base suffix (encodeWord 0)
        ((encodeWords (es.flatMap fun e => triples.flatMap
          (MachineClone100Table.cloneEquationWords e))).reverse ++ acc) (fun _ => [])⟩)
      ((2 + 3 * triples.length) *
        (encodeWords (es.flatMap SourceEncoding.equationWords)).length +
        (9 + 12 * triples.length) * es.length + 1) := by
  simpa only [recordsBits_equations, clonedRecordsBits_equations_table, List.length_map] using
    loopInTime_linear triples nonempty base suffix (es.map recordOfEquation) acc

end DFVSGames.Explicit.MachineClone100Loop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
