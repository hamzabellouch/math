import OAI.NumberTheory.TwoPoint.Bounds.RoughSieveCounts

namespace OAI

/-! Arbitrary bounded complex coefficients on the same rough support.
These are needed for the qualitative Fourier multiplier. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped ComplexConjugate Classical

noncomputable def weightedRoughFourier (Z : Finset ℕ) (c : ℕ → ℂ) (h : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  fourierPolynomial Z (fun z => (h : ℤ) * z) (fun z => c z / (z : ℂ))

lemma rough_coefficient_norm_le (Z : Finset ℕ) (c : ℕ → ℂ) (D : ℝ)
    (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ)) (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1)
    (z : ℕ) (hz : z ∈ Z) : ‖c z / (z : ℂ)‖ ≤ D⁻¹ := by
  rw [norm_div, Complex.norm_natCast]
  calc
    _ ≤ 1 / (z : ℝ) := div_le_div_of_nonneg_right (hc z hz) (Nat.cast_nonneg _)
    _ ≤ _ := by simpa only [one_div] using inv_anti₀ hD (hZ z hz)

theorem norm_weightedRoughFourier_le (Z : Finset ℕ) (c : ℕ → ℂ) (h : ℕ)
    (D : ℝ) (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ))
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1) (θ : AddCircle (1 : ℝ)) :
    ‖weightedRoughFourier Z c h θ‖ ≤ Z.card / D := by
  apply (norm_fourierPolynomial_le Z _ _ θ).trans
  calc
    _ ≤ ∑ _z ∈ Z, D⁻¹ := sum_le_sum (rough_coefficient_norm_le Z c D hD hZ hc)
    _ = _ := by simp [div_eq_mul_inv]

theorem weightedRoughFourier_fourth_le (Z : Finset ℕ) (c : ℕ → ℂ) (h : ℕ)
    (hh : 0 < h) (D : ℝ) (hD : 0 < D) (hZ : ∀ z ∈ Z, D ≤ (z : ℝ))
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1) :
    (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
      (additiveQuadruples Z).card * (D⁻¹) ^ 4 := by
  have hrel (q : (ℕ × ℕ) × (ℕ × ℕ)) :
      (h : ℤ) * q.1.1 + (h : ℤ) * q.1.2 =
        (h : ℤ) * q.2.1 + (h : ℤ) * q.2.2 ↔
      q.1.1 + q.1.2 = q.2.1 + q.2.2 := by
    rw [← mul_add, ← mul_add,
      mul_right_inj' (show (h : ℤ) ≠ 0 by exact_mod_cast hh.ne')]
    exact_mod_cast Iff.rfl
  rw [weightedRoughFourier, integral_norm_fourierPolynomial_fourth]
  simp_rw [hrel]
  rw [← sum_filter]
  calc
    _ ≤ ∑ _q ∈ additiveQuadruples Z, (D⁻¹) ^ 4 := by
      apply sum_le_sum
      intro q hq
      have hm := mem_additiveQuadruples hq
      have h₁ := rough_coefficient_norm_le Z c D hD hZ hc q.1.1 hm.1
      have h₂ := rough_coefficient_norm_le Z c D hD hZ hc q.1.2 hm.2.1
      have h₃ := rough_coefficient_norm_le Z c D hD hZ hc q.2.1 hm.2.2.1
      have h₄ := rough_coefficient_norm_le Z c D hD hZ hc q.2.2 hm.2.2.2.1
      calc
        _ ≤ ‖c q.1.1 / (q.1.1 : ℂ) * (c q.1.2 / (q.1.2 : ℂ)) *
            conj (c q.2.1 / (q.2.1 : ℂ) * (c q.2.2 / (q.2.2 : ℂ)))‖ :=
          Complex.re_le_norm _
        _ ≤ D⁻¹ * D⁻¹ * (D⁻¹ * D⁻¹) := by
          simp only [Complex.norm_conj, norm_mul]
          gcongr
        _ = _ := by ring
    _ = _ := by simp

theorem weightedRoughFourier_bounds_of_sieve (P Z : Finset ℕ) (c : ℕ → ℂ)
    (D h : ℕ) [NeZero D] (hh : 0 < h) (A B : ℝ)
    (hZ : ∀ z ∈ Z, D ≤ z ∧ z < D + D ∧ avoidsPrimeSet P z)
    (hc : ∀ z ∈ Z, ‖c z‖ ≤ 1)
    (h₁ : (uniformFiniteLaw (Fin D)).probability
      (fun j => avoidsPrimeSet P (D + j.val)) ≤ A)
    (h₄ : (uniformFiniteLaw (Fin D × Fin D × Fin D)).probability
      (fun j => fourFormsAvoidPrimeSet P
        (D + j.1.val, D + j.2.1.val, D + j.2.2.val)) ≤ B) :
    (∀ θ, ‖weightedRoughFourier Z c h θ‖ ≤ A) ∧
      (∫ θ, ‖weightedRoughFourier Z c h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤ B / D := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hzr (z : ℕ) (hz : z ∈ Z) : (D : ℝ) ≤ z := by exact_mod_cast (hZ z hz).1
  have hcard : (Z.card : ℝ) ≤ (D : ℝ) * A := by
    calc
      _ ≤ ((roughIntervalSamples P D D).card : ℝ) := by
        exact_mod_cast rough_subset_card_le P Z D D hZ
      _ = _ := roughIntervalSamples_probability P D D
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ hD.le
  have hquad : ((additiveQuadruples Z).card : ℝ) ≤ (D : ℝ) ^ 3 * B := by
    calc
      _ ≤ ((roughCubeSamples P (D, D, D) D).card : ℝ) := by
        exact_mod_cast rough_additiveQuadruples_card_le P Z D D hZ
      _ = _ := roughCubeSamples_probability P (D, D, D) D
      _ ≤ _ := mul_le_mul_of_nonneg_left h₄ (by positivity)
  constructor
  · intro θ
    apply (norm_weightedRoughFourier_le Z c h (D : ℝ) hD hzr hc θ).trans
    exact (div_le_iff₀ hD).mpr (by nlinarith only [hcard])
  · calc
      _ ≤ ((additiveQuadruples Z).card : ℝ) * ((D : ℝ)⁻¹) ^ 4 :=
        weightedRoughFourier_fourth_le Z c h hh (D : ℝ) hD hzr hc
      _ ≤ ((D : ℝ) ^ 3 * B) * ((D : ℝ)⁻¹) ^ 4 :=
        mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = _ := by field_simp

end TwoPointCorrelations

end OAI
