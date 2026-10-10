import OAI.Computability.UniqueGames.Machines.MachineClone100TableLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Headers

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineClone100Model

def parsedTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    Tape → List Bool
  | .input => suffix
  | .header => encodeWord n
  | .counter => encodeWord m
  | tape => base tape

/-- Exact header-stage endpoint. The occurrence counter is retained for the
body loop; generated output is accumulated in reverse. -/
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

private theorem twoFieldsTapes (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hheader : base .header = []) (hcounter : base .counter = []) :
    SourceMachine.afterField .input .counter
      (SourceMachine.afterField .input .header base n (encodeWord m ++ suffix)) m suffix =
      parsedTapes base n m suffix := by
  funext tape
  cases tape <;>
    simp [SourceMachine.afterField, SourceMachine.fieldTapes, parsedTapes, hheader, hcounter]

private theorem firstContextTapes (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool)
    (hreversed : base .reversed = []) :
    MachineClone100Context.contextTapes triples (.inl 0) (parsedTapes base n m suffix) =
      Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale, hreversed]

private theorem secondContextTapes (triples : List (Nat × Nat × Nat))
    (base : Tape → List Bool) (n m : Nat) (suffix : List Bool) :
    MachineClone100Context.contextTapes triples (.inl 1)
      (Function.update (parsedTapes base n m suffix) .reversed (encodeWord (100 * n)).reverse) =
      Function.update (parsedTapes base n m suffix) .reversed
        (encodeWords [100 * n, triples.length * m]).reverse := by
  simp [MachineClone100Context.contextTapes, contextSource, headerTape, parsedTapes,
    MachineClone100Affine.output_word, contextOffset, contextScale,
    encodeWords, List.reverse_append]

private theorem clearHeaderTapes (triples : List (Nat × Nat × Nat))
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
    twoFieldsTapes base n m suffix hheader hcounter
  rw [ht₁] at p₁
  have hs₁ : t₁ .scratch = [] := by simpa [t₁, parsedTapes] using hscratch
  have p₂ := MachineClone100Context.contextTrace triples hne (.inl 0) t₁ hs₁
    (initialState triples.length)
  have ht₂ : MachineClone100Context.contextTapes triples (.inl 0) t₁ = t₂ :=
    firstContextTapes triples base n m suffix hreversed
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
    secondContextTapes triples base n m suffix
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
    clearHeaderTapes triples base n m suffix
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

/-- The exact header trace packaged in the machine execution-time interface. -/
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

end UniqueGamesTheorem.Explicit.MachineClone100Headers

end

end OAI
