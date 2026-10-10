import OAI.NumberTheory.Ostmann.Construction.HistorySubstitution

namespace OAI

/-! # Reconstructing all erased pivots by their ordered substitutions -/

namespace Ostmann

open scoped Classical

namespace HistoryFormula

variable {σ : Type*}

noncomputable def replayFormulas (steps : List (σ × HistoryFormula σ))
    (env : σ → HistoryFormula σ) : σ → HistoryFormula σ :=
  match steps with
  | [] => env
  | step :: rest => replayFormulas rest (Function.update env step.1 (step.2.bind env))

noncomputable def replayValues (steps : List (σ × HistoryFormula σ)) (x : σ → ℚ) : σ → ℚ :=
  match steps with
  | [] => x
  | step :: rest => replayValues rest (Function.update x step.1 (step.2.value x))

theorem replayFormulas_value (steps : List (σ × HistoryFormula σ))
    (env : σ → HistoryFormula σ) (x : σ → ℚ) (i : σ) :
    (replayFormulas steps env i).value x = replayValues steps (fun j => (env j).value x) i := by
  induction steps generalizing env with
  | nil => rfl
  | cons step rest ih =>
    simp only [replayFormulas, replayValues, ih]
    have he : (fun j => (Function.update env step.1 (step.2.bind env) j).value x) =
        Function.update (fun j => (env j).value x) step.1 (step.2.value (fun j => (env j).value x)) := by
      funext j
      by_cases hj : j = step.1
      · subst j; simp only [Function.update_self, value_bind]
      · simp only [Function.update_of_ne hj]
    rw [he]

theorem replayFormulas_cost (steps : List (σ × HistoryFormula σ)) (C B : ℕ)
    (hC : 1 ≤ C) (hB : 1 ≤ B) (env : σ → HistoryFormula σ)
    (henv : ∀ i, (env i).cost ≤ B) (hsteps : ∀ step ∈ steps, step.2.cost ≤ C) (i : σ) :
    (replayFormulas steps env i).cost ≤ C ^ steps.length * B := by
  induction steps generalizing B env with
  | nil => simpa only [replayFormulas, List.length_nil, pow_zero, one_mul] using henv i
  | cons step rest ih =>
    let env' := Function.update env step.1 (step.2.bind env)
    have hB' : 1 ≤ C * B := by nlinarith
    have henv' : ∀ j, (env' j).cost ≤ C * B := by
      intro j
      by_cases hj : j = step.1
      · subst j
        simp only [env', Function.update_self]
        exact (cost_bind_le step.2 env B hB henv).trans
          (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left B (hsteps step (by simp)))
      · have hb : B ≤ C * B := by nlinarith
        simpa only [env', Function.update_of_ne hj] using (henv j).trans hb
    have hout := ih (C * B) hB' env' henv' (fun s hs => hsteps s (by simp [hs]))
    change (replayFormulas rest env' i).cost ≤ _
    simpa only [List.length_cons, pow_succ, Nat.mul_assoc] using hout

theorem replayFormulas_inputs (steps : List (σ × HistoryFormula σ))
    (env : σ → HistoryFormula σ) (R : ℝ) (henv : ∀ i, (env i).InputsBounded R)
    (hsteps : ∀ step ∈ steps, step.2.InputsBounded R) (i : σ) :
    (replayFormulas steps env i).InputsBounded R := by
  induction steps generalizing env with
  | nil => exact henv i
  | cons step rest ih =>
    apply ih (Function.update env step.1 (step.2.bind env))
    · intro j
      by_cases hj : j = step.1
      · subst j
        simpa only [Function.update_self] using
          inputsBounded_bind step.2 env R (hsteps step (by simp)) henv
      · simpa only [Function.update_of_ne hj] using henv j
    · exact fun s hs => hsteps s (by simp [hs])

noncomputable def reconstructedFormulas (steps : List (σ × HistoryFormula σ)) : σ → HistoryFormula σ :=
  replayFormulas steps prime

theorem reconstructedFormulas_value (steps : List (σ × HistoryFormula σ)) (x : σ → ℚ) (i : σ) :
    (reconstructedFormulas steps i).value x = replayValues steps x i := by
  simpa only [reconstructedFormulas, value_prime] using replayFormulas_value steps prime x i

theorem reconstructedFormulas_cost (steps : List (σ × HistoryFormula σ)) (C : ℕ) (hC : 1 ≤ C)
    (hsteps : ∀ step ∈ steps, step.2.cost ≤ C) (i : σ) :
    (reconstructedFormulas steps i).cost ≤ C ^ steps.length := by
  simpa only [reconstructedFormulas, Nat.mul_one] using
    replayFormulas_cost steps C 1 hC (by omega) prime (fun _ => le_rfl) hsteps i

end HistoryFormula
end Ostmann

end OAI
