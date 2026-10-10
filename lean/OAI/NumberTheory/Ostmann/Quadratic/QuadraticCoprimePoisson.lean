import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeMask

namespace OAI

/-! # Poisson summation with an exact coprimality condition

The divisor terms are retained individually. They are the terms truncated in
Heath-Brown (1995), Lemma 13, for both small-kernel and dual-kernel sums.
-/

namespace Ostmann

open scoped Classical BigOperators FourierTransform SchwartzMap

 theorem quadratic_scaled_poisson (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, ψ ((n : ℝ) / X)) = (X : ℂ) * ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X) := by
  have hp := (positiveDilate ψ X⁻¹ (inv_pos.mpr hX)).tsum_eq_tsum_fourier 0
  simpa [positiveDilate_apply, positiveDilate_fourier, inv_mul_eq_div,
    tsum_mul_left] using hp

 theorem quadratic_tsum_multiples {d : ℕ} (hd : d ≠ 0) (f : ℤ → ℂ) :
    (∑' n : ℤ, if (d : ℤ) ∣ n then f n else 0) = ∑' n : ℤ, f (d * n) := by
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  have hi : Function.Injective (fun n : ℤ => (d : ℤ) * n) := mul_right_injective₀ hd'
  have hs : Function.support (fun n : ℤ => if (d : ℤ) ∣ n then f n else 0) ⊆
      Set.range (fun n : ℤ => (d : ℤ) * n) := by
    intro n hn
    by_cases h : (d : ℤ) ∣ n
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, hk.symm⟩
    · simp [h] at hn
  simpa only [dvd_mul_right, ite_true] using (hi.tsum_eq hs).symm

 theorem quadratic_scaled_summable (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
  simpa only [positiveDilate_apply, inv_mul_eq_div] using
    schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))

 theorem quadratic_coprime_poisson {q : ℕ} [NeZero q]
    (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (1 : DirichletCharacter ℂ q) (n : ZMod q) * ψ ((n : ℝ) / X)) =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        ∑' n : ℤ, 𝓕 ψ ((n : ℝ) * X / d) := by
  have hs (d : ℕ) : Summable (fun n : ℤ => (ArithmeticFunction.moebius d : ℂ) *
      (if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0)) := by
    apply Summable.of_norm_bounded
      ((quadratic_scaled_summable ψ hX).mul_left ‖(ArithmeticFunction.moebius d : ℂ)‖)
    intro n
    split_ifs
    · simp only [norm_mul, le_refl]
    · simp only [mul_zero, norm_zero]
      positivity
  calc
    _ = ∑' n : ℤ, ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0) := by
      apply tsum_congr
      intro n
      rw [principal_character_moebius, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑' n : ℤ, if (d : ℤ) ∣ n then ψ ((n : ℝ) / X) else 0 := by
      rw [Summable.tsum_finsetSum (fun d _ => hs d)]
      simp only [tsum_mul_left]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
      rw [quadratic_tsum_multiples hd0]
      have he : (fun n : ℤ => ψ (((d * n : ℤ) : ℝ) / X)) =
          fun n : ℤ => ψ ((n : ℝ) / (X / d)) := by
        funext n
        congr 1
        push_cast
        field_simp
      rw [he, quadratic_scaled_poisson ψ (div_pos hX hdR)]
      simp only [mul_div_assoc, mul_assoc]

end Ostmann

end OAI
