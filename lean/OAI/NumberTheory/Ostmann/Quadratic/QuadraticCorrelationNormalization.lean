import OAI.NumberTheory.Ostmann.ZeroDensity.OriginalDensityCorrelation

namespace OAI

/-! # Exact cancellation of the quadratic-sum normalization on a dyadic segment -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem quadratic_normalization_product (R d e s v : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (hv : 0 < v) :
    Real.sqrt (R * d / (s * v)) * Real.sqrt (R * e / (s * v)) * s =
      R * Real.sqrt (d * e) / v := by
  have hx : 0 ≤ R / (s * v) := by positivity
  calc
    _ = Real.sqrt ((R * d / (s * v)) * (R * e / (s * v))) * s := by
      rw [Real.sqrt_mul (show 0 ≤ R * d / (s * v) by positivity)]
    _ = Real.sqrt ((R / (s * v)) ^ 2 * (d * e)) * s := by
      congr 2
      ring
    _ = (R / (s * v)) * Real.sqrt (d * e) * s := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx]
    _ = _ := by field_simp

theorem quadratic_normalization_cancel (R d e s v : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (hv : 0 < v)
    (A B : ℂ) :
    (((Real.sqrt (R * d / (s * v)) : ℝ) : ℂ)⁻¹ * A) *
      conj (((Real.sqrt (R * e / (s * v)) : ℝ) : ℂ)⁻¹ * B) / (s : ℂ) =
        ((v / (R * Real.sqrt (d * e)) : ℝ) : ℂ) * (A * conj B) := by
  have hp := quadratic_normalization_product R d e s v hR hd he hs hv
  have hde : 0 < Real.sqrt (d * e) := Real.sqrt_pos.mpr (mul_pos hd he)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hdeC : (Real.sqrt (d * e) : ℂ) ≠ 0 := by exact_mod_cast hde.ne'
  have hprod : (Real.sqrt (R * d / (s * v)) : ℂ) *
      (Real.sqrt (R * e / (s * v)) : ℂ) * (s : ℂ) =
        (R : ℂ) * (Real.sqrt (d * e) : ℂ) / (v : ℂ) := by exact_mod_cast hp
  simp only [map_mul, map_inv₀, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (R * d / (s * v)) : ℂ) *
        (Real.sqrt (R * e / (s * v)) : ℂ) * (s : ℂ))⁻¹ * (A * conj B) := by
      simp only [mul_inv_rev, div_eq_mul_inv]
      ring
    _ = _ := by
      rw [hprod]
      push_cast
      field_simp

/-- After cancellation the remaining finite sum has a constant positive
normalization, independent of the kernel index. -/
theorem quadratic_normalized_correlation_bound {ι : Type*}
    (S : Finset ι) (σ : ι → ℝ) (A B : ι → ℂ) (R d e v C : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v)
    (hσ : ∀ s ∈ S, 0 < σ s)
    (hcor : ‖∑ s ∈ S, A s * conj (B s)‖ ≤ C) :
    ‖∑ s ∈ S,
      (((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * A s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * B s) / (σ s : ℂ)‖ ≤
      v / (R * Real.sqrt (d * e)) * C := by
  have hn : 0 ≤ v / (R * Real.sqrt (d * e)) := by positivity
  have heq : (∑ s ∈ S,
      (((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * A s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * B s) / (σ s : ℂ)) =
      ((v / (R * Real.sqrt (d * e)) : ℝ) : ℂ) * ∑ s ∈ S, A s * conj (B s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact quadratic_normalization_cancel R d e (σ s) v hR hd he (hσ s hs) hv (A s) (B s)
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left hcor hn

end Ostmann

end OAI
