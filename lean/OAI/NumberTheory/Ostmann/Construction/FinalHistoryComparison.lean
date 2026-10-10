import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCorrelations

namespace OAI

/-! # Combining the actual history correlations under the original final prior -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem final_history_comparison {Y A H : Type*} [Fintype Y] [Fintype A]
    (n m : ℕ) (ν : Y → ℝ) (μ : A → ℝ) (hν : ∀ y, 0 ≤ ν y) (hμ : ∀ a, 0 ≤ μ a)
    (hμmass : ∑ a, μ a = 1) (T B E : ℝ) (hT : ∑ y, ν y ≤ T) (hE : 0 ≤ E)
    (S : Finset H) (a : H → (Y × ((ParityPathSum n × Fin m) → A)) → ℂ)
    (henergy : (∑ x, finalBulkPrior n m ν μ x * ‖∑ h ∈ S, a h x‖ ^ 2) ≤ B)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f → ∀ h ∈ S, ∀ k ∈ S,
      ‖∑ x, (finalBulkPrior n m ν μ x : ℂ) *
        (a h (finalSamplePerm e x) * conj (a k (finalSamplePerm f x)))‖ ≤ E) :
    ‖∑ x, (finalBulkPrior n m ν μ x : ℂ) * (∑ h ∈ S, a h x)‖ ^ 2 ≤
      T * (B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + (S.card : ℝ) ^ 2 * E) := by
  let F := fun x => ∑ h ∈ S, a h x
  apply final_actual_prior_comparison n m ν μ hν hμ hμmass T B ((S.card : ℝ) ^ 2 * E)
    hT (mul_nonneg (sq_nonneg _) hE) F
  intro e f
  by_cases hef : e = f
  · subst f
    simp only
    rw [show (∑ x, (finalBulkPrior n m ν μ x : ℂ) *
        (finalReassignedValue F e x * star (finalReassignedValue F e x))) =
        ∑ x, (finalBulkPrior n m ν μ x : ℂ) *
          (finalReassignedValue F e x * conj (finalReassignedValue F e x)) by rfl]
    rw [diagonal_pair_eq_energy _ (finalBulkPrior_nonneg ν μ hν hμ), finalReassignedValue_energy]
    exact henergy
  · simp only [ite_eq_right hef]
    have hh := finite_history_pair_bound (finalBulkPrior n m ν μ) S S
      (fun h x => a h (finalSamplePerm e x)) (fun h x => a h (finalSamplePerm f x)) E
      (hpair e f hef)
    simpa only [F, finalReassignedValue, pow_two, mul_assoc, Complex.star_def] using hh

end Ostmann

end OAI
