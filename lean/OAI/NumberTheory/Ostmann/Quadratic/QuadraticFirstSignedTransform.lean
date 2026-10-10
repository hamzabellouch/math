import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSignedInfiniteSum
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstMomentTransform

namespace OAI

/-! # The actual nonzero first frequencies in signed squarefree coordinates -/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

theorem quadratic_jacobi_frequency_summable (ψ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y)
    (e q : ℕ) :
    Summable (fun h : ℤ => (jacobiSym ((e : ℤ) * h) q : ℂ) * ψ ((h : ℝ) * Y)) := by
  have hs := quadratic_scaled_summable ψ (inv_pos.mpr hY)
  simp only [div_inv_eq_mul] at hs
  apply Summable.of_norm_bounded hs
  intro h
  have hJ : ‖(jacobiSym ((e : ℤ) * h) q : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy ((e : ℤ) * h) q with he | he | he <;> rw [he] <;> norm_num
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)).trans_eq (one_mul _)

theorem quadratic_first_signed_transform {q e : ℕ} (hq : 1 < q) (he : 0 < e)
    {M : ℝ} (hM : 0 < M) (ψ : 𝓢(ℝ, ℂ)) :
    (∑' h : ℤ, (jacobiSym ((e : ℤ) * h) q : ℂ) *
      𝓕 ψ ((h : ℝ) * M / ((e : ℝ) * q))) =
    ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), ∑' b : QuadraticOddKernel, ∑' c : ℕ+,
      (jacobiSym ((e : ℤ) * (a * (c : ℕ) ^ 2 * (b.val : ℕ))) q : ℂ) *
        𝓕 ψ (((a * (c : ℕ) ^ 2 * (b.val : ℕ) : ℤ) : ℝ) * M / ((e : ℝ) * q)) := by
  apply quadratic_signed_tsum_iterated
  · simp only [mul_zero, Int.cast_zero, zero_mul, zero_div, jacobiSym.zero_left hq]
  · have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    simpa only [mul_div_assoc] using quadratic_jacobi_frequency_summable (𝓕 ψ)
      (div_pos hM (mul_pos heR hqR)) e q

end Ostmann

end OAI
