import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructionFrequencyPeriod

namespace OAI

/-! # Bounds for every intermediate test in the actual substitution order -/

namespace Ostmann

open scoped Classical

theorem reconstructionTests_cost {σ : Type*} (steps : List (HistoryPivotStep σ))
    (env : σ → HistoryFormula σ) (C B : ℕ) (hC : 1 ≤ C) (hB : 1 ≤ B)
    (henv : ∀ i, (env i).cost ≤ B)
    (hsteps : ∀ step ∈ steps, step.formula.cost ≤ C) :
    ∀ F ∈ reconstructionTests steps env, F.cost ≤ C ^ steps.length * B := by
  induction steps generalizing env B with
  | nil => simp only [reconstructionTests, List.not_mem_nil, false_implies, implies_true]
  | cons step rest ih =>
    have hhead : (step.formula.bind env).cost ≤ C * B := by
      exact (HistoryFormula.cost_bind_le step.formula env B hB henv).trans
        (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left B (hsteps step (by simp)))
    have henv' : ∀ i, (Function.update env step.target (step.formula.bind env) i).cost ≤ C * B := by
      intro i
      by_cases hi : i = step.target
      · subst i; simpa only [Function.update_self] using hhead
      · simpa only [Function.update_of_ne hi] using
          (henv i).trans (by nlinarith)
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · have hp : 1 ≤ C ^ rest.length := Nat.one_le_pow rest.length C (by omega)
      simp only [List.length_cons, pow_succ]
      nlinarith
    · have hh := ih _ (C * B) (by nlinarith) henv'
        (fun s hs => hsteps s (by simp [hs])) F hF
      simpa only [List.length_cons, pow_succ, Nat.mul_assoc] using hh

theorem reconstructionTests_frequencies_dvd {σ : Type*} (steps : List (HistoryPivotStep σ))
    (env : σ → HistoryFormula σ) (M : ℤ)
    (henv : ∀ i d, d ∈ (env i).frequencies → d ∣ M)
    (hsteps : ∀ step ∈ steps, step.s ∣ M) :
    ∀ F ∈ reconstructionTests steps env, ∀ d ∈ F.frequencies, d ∣ M := by
  induction steps generalizing env with
  | nil => simp only [reconstructionTests, List.not_mem_nil, false_implies, implies_true]
  | cons step rest ih =>
    have hhead := HistoryFormula.frequencies_bind_dvd step.formula env M
      (step.formula_frequencies_dvd M (hsteps step (by simp))) henv
    have henv' : ∀ i d, d ∈ (Function.update env step.target (step.formula.bind env) i).frequencies → d ∣ M := by
      intro i d hd
      by_cases hi : i = step.target
      · subst i; simp only [Function.update_self] at hd; exact hhead d hd
      · simp only [Function.update_of_ne hi] at hd; exact henv i d hd
    intro F hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact hhead
    · exact ih _ henv' (fun s hs => hsteps s (by simp [hs])) F hF

theorem reconstructionTests_prime_period {σ : Type*} (steps : List (HistoryPivotStep σ))
    (M s : ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hsteps : ∀ step ∈ steps, step.s ∣ M)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (hs : s ∣ M) (F : HistoryFormula σ)
    (hF : F ∈ reconstructionTests steps HistoryFormula.prime) :
    F.cleared.denominator * s ∣ M ^ (C ^ steps.length + 1) := by
  have hc : F.cost ≤ C ^ steps.length := by
    simpa only [Nat.mul_one] using reconstructionTests_cost steps .prime C 1 hC (by omega)
      (fun _ => le_rfl) (fun step hstep => by simpa only [step.formula_cost] using hsize step hstep) F hF
  have hf := reconstructionTests_frequencies_dvd steps .prime M
    (by intro i d hd; simp only [HistoryFormula.frequencies, List.not_mem_nil] at hd) hsteps F hF
  exact (F.denominator_test_period M s hf hs).trans
    (pow_dvd_pow M (Nat.add_le_add_right (F.frequency_count_le_cost.trans hc) 1))

end Ostmann

end OAI
