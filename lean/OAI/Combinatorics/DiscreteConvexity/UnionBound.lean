import OAI.Combinatorics.DiscreteConvexity.ProbabilisticExistence

namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity.FiniteLaw

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- The indexed union bound uses no independence among the events. -/
theorem prob_exists_le (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    μ.prob (fun ω => ∃ i, P i ω) ≤ ∑ i, μ.prob (P i) := by
  classical
  calc
    μ.prob (fun ω => ∃ i, P i ω) ≤
        μ.expectation (fun ω => ∑ i, if P i ω then (1 : ℝ) else 0) := by
      apply μ.prob_le_expectation
      · intro ω
        exact Finset.sum_nonneg fun i _ => by
          by_cases h : P i ω <;> simp [h]
      · intro ω hω
        obtain ⟨i, hi⟩ := hω
        have hsum : (if P i ω then (1 : ℝ) else 0) ≤
            ∑ j, if P j ω then (1 : ℝ) else 0 := by
          apply Finset.single_le_sum (a := i)
            (f := fun j => if P j ω then (1 : ℝ) else 0)
          · intro j _
            by_cases h : P j ω <;> simp [h]
          · exact Finset.mem_univ i
        simpa only [ite_eq_left hi] using hsum
    _ = ∑ i, μ.prob (P i) := by
      rw [μ.expectation_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (μ.prob_eq_expectation (P i)).symm

/-- Simultaneous success is bounded using only the individual marginals. -/
theorem prob_forall_ge (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    1 - ∑ i, (1 - μ.prob (P i)) ≤ μ.prob (fun ω => ∀ i, P i ω) := by
  classical
  have hbad := prob_exists_le μ (fun i ω => ¬ P i ω)
  have hcompl : μ.prob (fun ω => ¬ ∀ i, P i ω) ≤
      ∑ i, μ.prob (fun ω => ¬ P i ω) := by
    simpa only [not_forall] using hbad
  rw [μ.prob_compl] at hcompl
  simp_rw [μ.prob_compl] at hcompl
  linarith

theorem prob_forall_ge_of_const (μ : FiniteLaw Ω) (P : ι → Ω → Prop)
    (a : ℝ) (hmarginal : ∀ i, μ.prob (P i) = a) :
    1 - (Fintype.card ι : ℝ) * (1 - a) ≤ μ.prob (fun ω => ∀ i, P i ω) := by
  have h := prob_forall_ge μ P
  simpa only [hmarginal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem exists_forall_of_const (μ : FiniteLaw Ω) (P : ι → Ω → Prop)
    (a : ℝ) (hmarginal : ∀ i, μ.prob (P i) = a)
    (hbudget : (Fintype.card ι : ℝ) * (1 - a) < 1) :
    ∃ ω, ∀ i, P i ω := by
  apply exists_of_prob_pos μ (P := fun ω => ∀ i, P i ω)
  have h := prob_forall_ge_of_const μ P a hmarginal
  linarith

end TalagrandDiscreteConvexity.FiniteLaw

end OAI
