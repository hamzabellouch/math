import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplificationMean
import OAI.NumberTheory.Ostmann.Construction.PhysicalAmplification

namespace OAI

/-! # Poisson summation gives the exact total amplification weight -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

theorem scaled_periodic_poisson {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)) =
      (X : ℂ) * ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X / N) * additiveFourier F (-(n : ZMod N)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have ha : 0 < (N : ℝ) / X := div_pos hN hX
  have hp := integer_poisson_transform (positiveDilate ψ ((N : ℝ) / X) ha) F
  have harg (n : ℤ) : (N : ℝ) / X * ((n : ℝ) / N) = n / X := by field_simp
  have hfreq (n : ℤ) : (n : ℝ) / ((N : ℝ) / X) = n * X / N := by rw [div_div_eq_mul_div]
  simp_rw [positiveDilate_apply, harg, positiveDilate_fourier, hfreq] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp

theorem periodic_poisson_single_frequency {N : ℕ} [NeZero N]
    (F : ZMod N → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hmean : additiveFourier F 0 = 1) (hH : H < X / N)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, F (n : ZMod N) * ψ ((n : ℝ) / X)) = (X : ℂ) * 𝓕 ψ 0 := by
  rw [scaled_periodic_poisson F ψ X hX]
  have hn (n : ℤ) (hne : n ≠ 0) :
      𝓕 ψ ((n : ℝ) * X / N) * additiveFourier F (-(n : ZMod N)) = 0 := by
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |n| by have hh := abs_pos.mpr hne; omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    have hlarge : H < |(n : ℝ) * X / N| := by
      rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hN]
      have hb := mul_le_mul_of_nonneg_right habs (div_nonneg hX.le hN.le)
      have he : |(n : ℝ)| * X / N = |(n : ℝ)| * (X / N) := by ring
      rw [he]
      exact hH.trans_le (by simpa only [one_mul] using hb)
    rw [hsupp _ hlarge, zero_mul]
  rw [tsum_eq_single 0 hn]
  simp [hmean]

/-- Exact form of the total-weight identity for the manuscript's original
positive periodic weight. -/
theorem amplification_total_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (hH : H < X / Q.toList.prod) (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, physicalWeight Q D ψ X n) = X * (𝓕 ψ 0).re := by
  let : NeZero Q.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime Q hQ)).ne'⟩
  have hp := periodic_poisson_single_frequency (amplificationCRT Q hQ D) ψ X H hX
    (amplificationCRT_mean_one Q hQ D) hH hsupp
  have hsc : Summable (fun n : ℤ => amplificationCRT Q hQ D (n : ZMod Q.toList.prod) * ψ ((n : ℝ) / X)) := by
    have hsn : Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
      simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
        schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
    apply Summable.of_norm_bounded (hsn.mul_left ((17 / 16 : ℝ) ^ Q.card))
    intro n
    rw [amplificationCRT_intCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (amplificationWeight_pos Q hQ D n)]
    exact mul_le_mul_of_nonneg_right (amplificationWeight_le Q hQ D n) (norm_nonneg _)
  have hre := congrArg Complex.reCLM hp
  rw [Complex.reCLM.map_tsum hsc] at hre
  simpa only [amplificationCRT_intCast, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, physicalWeight, mul_comm] using hre

end Ostmann

end OAI
