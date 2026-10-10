import OAI.Computability.UniqueGames.Machines.MachineLookupCore

namespace OAI

section

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

private theorem discard_update_twice (source : K) (base : K → List Bool)
    (input replacement : List Bool) :
    Function.update (Function.update base source input) source replacement =
      Function.update base source replacement := by
  funext p
  by_cases hp : p = source
  · subst p; simp
  · simp [hp]

theorem discardStep_delimiter (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (false :: suffix)⟩ =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (false :: suffix))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discardStep_true (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (input : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (true :: input)⟩ =
      some ⟨some loopLabel, (ambient, some true), Function.update base source input⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (true :: input))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

/-- EOF returns to the guard in one transition, without changing any tape. -/
theorem discard_empty_step (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (hinput : base source = [])
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register), base⟩ =
      some ⟨some returnLabel, (ambient, none), base⟩ := by
  have hupdate : Function.update base source [] = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  change some (TM2.stepAux (program loopLabel) (ambient, register) base) = _
  rw [atLoop]
  simp [discard, TM2.stepAux, hinput, hupdate]

/-- A normalized tape form for the field-discard trace. -/
theorem discardTrace_update (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        Function.update base source (encodeWord n ++ suffix)⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  induction n generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      discardStep_delimiter source loopLabel returnLabel program atLoop
        base suffix ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        Function.update base source (true :: (encodeWord n ++ suffix))⟩) = _
    rw [discardStep_true source loopLabel returnLabel program atLoop, ih]

/-- Discard exactly the first encoded field, in one transition per payload bit
plus one transition for its delimiter. No condition is imposed on other tapes. -/
theorem discardTrace (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  have hbase : Function.update base source (encodeWord n ++ suffix) = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  have h := discardTrace_update source loopLabel returnLabel program atLoop
    base n suffix ambient register
  rw [hbase] at h
  exact h

/-- The same exact trace packaged for composition with ambient machine phases. -/
def discardInTime (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := discardTrace source loopLabel returnLabel program atLoop
    base n suffix hinput ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineLookup

end

end OAI
