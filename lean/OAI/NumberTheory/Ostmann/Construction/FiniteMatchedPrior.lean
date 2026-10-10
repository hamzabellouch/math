import OAI.NumberTheory.Ostmann.Arithmetic.MatchedPriorCorrelation

namespace OAI

/-! # The counterpart harmonic normalization on the actual finite slot type -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_enumeration_sum {A M : Type*} [AddCommMonoid M]
    (F G : Fintype A) (f : A → M) :
    Finset.sum (@Finset.univ A F) f = Finset.sum (@Finset.univ A G) f := by
  cases Subsingleton.elim F G
  rfl

theorem finite_matched_harmonic_prior {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (e : Equiv.Perm H) (x : H → P) :
    (∏ i, primeSubsetPrior P (Q i) (x (e i))) =
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ *
        ∏ i, (if (x i : ℕ) ∈ Q (e.symm i) then (1 : ℝ) else 0) := by
  have hi (i : H) : primeSubsetPrior P (Q i) (x (e i)) =
      (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x (e i) : ℝ)⁻¹ *
        (if (x (e i) : ℕ) ∈ Q (e.symm (e i)) then (1 : ℝ) else 0) := by
    simp only [primeSubsetPrior, e.symm_apply_apply]
    split_ifs <;> simp only [mul_one, mul_zero]
    ring
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Equiv.prod_comp e (fun i => (x i : ℝ)⁻¹),
    Equiv.prod_comp e (fun i => if (x i : ℕ) ∈ Q (e.symm i) then (1 : ℝ) else 0),
    Finset.prod_inv_distrib]
  simp only [Finset.prod_inv_distrib]

/-- This keeps the reciprocal product scale outside the normalized pair
correlation, before any sum over integer pivots. -/
theorem finite_matched_harmonic_correlation_eq {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (e : Equiv.Perm H)
    (μ : (H → P) → ℝ) (G : (H → P) → ℂ) (X : ℝ) (hX : X ≠ 0) :
    (∑ x, (μ x : ℂ) * (∏ i, primeSubsetPrior P (Q i) (x (e i)) : ℝ) * G x) =
      (((∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * X⁻¹ : ℝ) : ℂ) *
        ∑ x, (μ x : ℂ) * ((X / (∏ i, (x i : ℝ)) : ℝ) : ℂ) *
          ((∏ i, if (x i : ℕ) ∈ Q (e.symm i) then (1 : ℝ) else 0) : ℂ) * G x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [finite_matched_harmonic_prior]
  have he (C H R : ℝ) : C * H⁻¹ * R = (C * X⁻¹) * (X / H) * R := by
    rw [div_eq_mul_inv]
    calc
      _ = C * (X⁻¹ * X) * H⁻¹ * R := by rw [inv_mul_cancel₀ hX]; ring
      _ = _ := by ring
  rw [he]
  push_cast
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
  ring

theorem finite_matched_harmonic_correlation_bound {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (e : Equiv.Perm H)
    (μ : (H → P) → ℝ) (G : (H → P) → ℂ) (X δ : ℝ) (hX : 0 < X)
    (hbound : ‖∑ x, (μ x : ℂ) * ((X / (∏ i, (x i : ℝ)) : ℝ) : ℂ) *
      ((∏ i, if (x i : ℕ) ∈ Q (e.symm i) then (1 : ℝ) else 0) : ℂ) * G x‖ ≤ δ) :
    ‖∑ x, (μ x : ℂ) * (∏ i, primeSubsetPrior P (Q i) (x (e i)) : ℝ) * G x‖ ≤
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * X⁻¹ * δ := by
  rw [finite_matched_harmonic_correlation_eq P Q e μ G X hX.ne', norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Ostmann

end OAI
