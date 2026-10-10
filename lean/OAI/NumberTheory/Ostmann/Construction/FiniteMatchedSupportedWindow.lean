import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedWindow

namespace OAI

/-! # Counterpart normalization on the live coefficient support -/
namespace Ostmann
open scoped Classical BigOperators

theorem finite_matched_supported_window_eq {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ)
    (Z : ℝ) (hZ : 0 < Z) (hscale : ∀ x, F x ≠ 0 → Z ≤ ∏ h, (x (.inl h) : ℝ)) :
    (∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x) =
    (((∏ h, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ : ℝ) : ℂ) *
      ∑ x : H ⊕ Y → P, ((Z / (∏ h, (x (.inl h) : ℝ)) : ℝ) : ℂ) *
        (if Z ≤ ∏ h, (x (.inl h) : ℝ) then
          ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
          (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) * F x)
        else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hF : F x = 0
  · simp only [hF, mul_zero, ite_self]
  by_cases hx : (∏ i, primeSubsetPrior P (Q i) (x i)) = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
    split_ifs <;> simp only [mul_zero]
  · have hs := hscale x hF
    rw [ite_eq_left hs, finite_matched_harmonic_prior P (fun h => Q (.inl h)) e
      (fun h => x (.inl h))]
    have he (C D U : ℝ) : C * D⁻¹ * U = (C * Z⁻¹) * (Z / D) * U := by
      rw [div_eq_mul_inv]
      field_simp
    rw [he]
    push_cast
    simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    ring

theorem finite_matched_supported_window_bound {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ)
    (Z : ℝ) (hZ : 0 < Z) (hscale : ∀ x, F x ≠ 0 → Z ≤ ∏ h, (x (.inl h) : ℝ)) (δ : ℝ)
    (hbound : ‖∑ x : H ⊕ Y → P, ((Z / (∏ h, (x (.inl h) : ℝ)) : ℝ) : ℂ) *
        (if Z ≤ ∏ h, (x (.inl h) : ℝ) then
          ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
          (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) * F x)
        else 0)‖ ≤ δ) :
    ‖∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x‖ ≤
        (∏ h, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ * δ := by
  rw [finite_matched_supported_window_eq P Q e F Z hZ hscale, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Ostmann

end OAI
