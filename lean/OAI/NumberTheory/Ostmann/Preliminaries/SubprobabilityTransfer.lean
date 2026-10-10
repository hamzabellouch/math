import OAI.NumberTheory.Ostmann.Preliminaries.TransferCauchy

namespace OAI

/-! # Cauchy--Schwarz retains the internal distinctness restriction -/

namespace Ostmann

open scoped BigOperators

theorem subprobability_weighted_norm_sq_le {A : Type*} [Fintype A]
    (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a ≤ 1) (F : A → ℂ) :
    ‖∑ a, (μ a : ℂ) * F a‖ ^ 2 ≤ ∑ a, μ a * ‖F a‖ ^ 2 := by
  have hnorm : ‖∑ a, (μ a : ℂ) * F a‖ ≤ ∑ a, μ a * ‖F a‖ := by
    calc
      _ ≤ ∑ a, ‖(μ a : ℂ) * F a‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ _)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => Real.sqrt (μ a)) (fun a => Real.sqrt (μ a) * ‖F a‖)
  have hsq (a : A) : Real.sqrt (μ a) ^ 2 = μ a := Real.sq_sqrt (hμ a)
  have hprod (a : A) : Real.sqrt (μ a) * (Real.sqrt (μ a) * ‖F a‖) = μ a * ‖F a‖ := by
    rw [← mul_assoc, ← pow_two, hsq]
  simp only [mul_pow, hsq, hprod] at hCS
  have hpos : 0 ≤ ∑ a, μ a * ‖F a‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hbound := hCS.trans (mul_le_of_le_one_left hpos hmass)
  have hn : 0 ≤ ∑ a, μ a * ‖F a‖ :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hμ a) (norm_nonneg _))
  nlinarith [norm_nonneg (∑ a, (μ a : ℂ) * F a)]

theorem subprobability_transfer_row_bound {A : Type*} [Fintype A] {T : A → Type*}
    [∀ a, Fintype (T a)] (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hmass : ∑ a, μ a ≤ 1)
    (row coefficient : ∀ a, T a → ℂ) (M : A → ℝ)
    (hrow : ∀ a, (∑ t, ‖row a t‖ ^ 2) ≤ M a) :
    ‖∑ a, (μ a : ℂ) * ∑ t, row a t * coefficient a t‖ ^ 2 ≤
      ∑ a, μ a * (M a * ∑ t, ‖coefficient a t‖ ^ 2) := by
  apply (subprobability_weighted_norm_sq_le μ hμ hmass _).trans
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hμ a)
  exact (complex_pairing_sq_le (row a) (coefficient a)).trans
    (mul_le_mul_of_nonneg_right (hrow a) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end Ostmann

end OAI
