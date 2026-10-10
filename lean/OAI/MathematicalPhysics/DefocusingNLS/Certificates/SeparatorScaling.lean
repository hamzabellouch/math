import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RootDiskApplication

namespace OAI

/-! # Scaling between the integer certificate and the zero-tail polynomial -/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

noncomputable section

theorem scaled_monomial (a D : ℂ) (hD : D ≠ 0) (n : ℕ) (hn : n ≤ 15) :
    monomial n (a * D ^ (15 - n)) =
      C (D ^ 15) * (monomial n a).comp (C D⁻¹ * X) := by
  rw [← C_mul_X_pow_eq_monomial, monomial_comp, mul_pow, ← C_pow,
    pow_sub₀ D hD hn, ← inv_pow]
  simp only [map_mul]
  ring

theorem scaledSeparatorPolynomial_identity (ℓ : ℕ) :
    (scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex =
      C ((diskScale : ℂ) ^ 15) *
        ((windingPolynomial ℓ).map (Int.castRingHom ℂ)).comp
          (C (diskScale : ℂ)⁻¹ * X) := by
  classical
  simp only [scaledSeparatorPolynomial, windingPolynomial, Polynomial.map_sum, map_monomial,
    Int.cast_mul, Int.cast_pow, sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simpa using scaled_monomial (windingCoefficient ℓ n : ℂ) (diskScale : ℂ)
    (by norm_num [diskScale]) n (by
    have := Finset.mem_range.mp hn
    omega)

theorem scaledSeparatorPolynomial_roots (ℓ : ℕ) :
    ((scaledSeparatorPolynomial ℓ).map GaussianInt.toComplex).roots =
      (((windingPolynomial ℓ).map (Int.castRingHom ℂ)).roots.map
        (fun z => (diskScale : ℂ) * z)) := by
  rw [scaledSeparatorPolynomial_identity, roots_C_mul _ (by norm_num [diskScale])]
  have h := roots_comp_C_mul_X_add_C
    ((windingPolynomial ℓ).map (Int.castRingHom ℂ)) (diskScale : ℂ)⁻¹ 0
    (isUnit_iff_ne_zero.mpr (by norm_num [diskScale]))
  simpa only [map_zero, add_zero, sub_zero, Ring.inverse_eq_inv, inv_inv] using h

theorem closed_half_plane_count_image_pos (S : Finset ℂ) (d : ℝ) (hd : 0 < d) :
    ((S.image (fun z => (d : ℂ) * z)).filter (fun z => 0 ≤ z.re)).card =
      (S.filter (fun z => 0 ≤ z.re)).card := by
  classical
  rw [Finset.filter_image]
  have hinj : Function.Injective (fun z : ℂ => (d : ℂ) * z) := by
    intro z w h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hd.ne') h
  rw [Finset.card_image_of_injective _ hinj]
  congr 1
  ext z
  simp only [Finset.mem_filter, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, mul_nonneg_iff_of_pos_left hd]

/-- Exact half-plane count for the unscaled polynomial appearing in the
manuscript's zero-tail winding argument. -/
theorem windingPolynomial_closed_half_plane_count (ℓ : Fin 4) :
    ((((windingPolynomial ℓ).map (Int.castRingHom ℂ)).roots.toFinset).filter
      (fun z => 0 ≤ z.re)).card = positiveRootCount ℓ := by
  have h := zero_tail_closed_half_plane_count ℓ
  rw [scaledSeparatorPolynomial_roots, Multiset.toFinset_map] at h
  rw [show (diskScale : ℂ) = ((diskScale : ℝ) : ℂ) by norm_cast] at h
  rw [closed_half_plane_count_image_pos _ (diskScale : ℝ)
    (by norm_num [diskScale])] at h
  exact h

end
end DefocusingNLS.SeparatorArithmetic

end OAI
