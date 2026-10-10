import OAI.NumberTheory.Ostmann.Characters.NormalizedCharacterPoisson
import OAI.NumberTheory.Ostmann.Construction.OriginalSignedFourier
import OAI.NumberTheory.Ostmann.Construction.PhysicalAmplification

namespace OAI

/-! # Poisson transfer of the original amplified character sum -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem bounded_schwartz_lattice_summable (b : ℤ → ℂ) (B : ℝ)
    (hb : ∀ n, ‖b n‖ ≤ B) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    Summable (fun n : ℤ => b n * ψ ((n : ℝ) / X)) := by
  have hsn : Summable (fun n : ℤ => ‖ψ ((n : ℝ) / X)‖) := by
    simpa only [positiveDilate_apply, div_eq_mul_inv, mul_comm] using
      schwartz_int_norm_summable (positiveDilate ψ X⁻¹ (inv_pos.mpr hX))
  apply Summable.of_norm_bounded (hsn.mul_left B)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _)

theorem norm_jacobiComplex_int_le (n : ℤ) (M : ℕ) : ‖(jacobiSym n M : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy n M with h | h | h <;> rw [h] <;> norm_num

theorem primeDivisorDensity_norm (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (x : ZMod U.toList.prod) : ‖primeDivisorDensity Q hQ D U x‖ ≤ 1 := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  rw [primeDivisorDensity, dite_eq_left hU]
  exact (densityCRTList U.toList (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
    (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).norm_le_one x

theorem amplified_jacobi_poisson (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) [NeZero M]
    (hcop : Q.toList.prod.Coprime M) (hM : Squarefree M) (hodd : Odd M)
    (t : ZMod M) (hlift : (Q.toList.prod : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X)) =
      (Real.sqrt X : ℂ) * jacobiGaussPhase M *
        originalSignedFourier Q hQ D M h₀ ((t.val : ℝ) / M) ((M : ℝ) / X) (𝓕 ψ) := by
  classical
  have hsum (U : Finset ℕ) (hU : U ∈ Q.powerset) : Summable (fun n : ℤ =>
      (1 / 16 : ℂ) ^ U.card * (primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) *
        (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X))) := by
    apply Summable.mul_left
    apply bounded_schwartz_lattice_summable _ 1 _ ψ X hX
    intro n
    rw [norm_mul]
    exact (mul_le_mul (primeDivisorDensity_norm Q hQ D U (Finset.mem_powerset.mp hU) _)
      (norm_jacobiComplex_int_le _ M) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  calc
    _ = ∑' n : ℤ, ∑ U ∈ Q.powerset,
        (1 / 16 : ℂ) ^ U.card * (primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) *
          (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X)) := by
      apply tsum_congr
      intro n
      rw [amplificationWeight_expansion Q hQ D n, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ = ∑ U ∈ Q.powerset, (1 / 16 : ℂ) ^ U.card *
        ∑' n : ℤ, primeDivisorDensity Q hQ D U (n : ZMod U.toList.prod) *
          (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X) := by
      rw [Summable.tsum_finsetSum hsum]
      simp only [tsum_mul_left]
    _ = _ := by
      unfold originalSignedFourier
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      have hsub := Finset.mem_powerset.mp hU
      have hd := primeSet_prod_dvd_of_subset Q U hsub
      let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
        (primeSet_list_prime U (fun p hp => hQ p (hsub hp)))).ne'⟩
      have hdu : (U.toList.prod : ℤ) ∣ (Q.toList.prod : ℤ) := by exact_mod_cast hd
      rw [normalized_jacobi_poisson (hcop.of_dvd_left hd) hM hodd
        (primeDivisorDensity Q hQ D U) t h₀ (hdu.trans hlift) ψ X hX]
      simp only [primeDivisorSignedFrequency, dite_eq_left hsub,
        quadraticSymbolCoefficient, quadraticInverseResidue]
      push_cast
      ring

/-- The actual amplified physical sum is controlled by the original positive
Fourier statistic with its exact square-root scale. -/
theorem amplified_jacobi_positive_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ) [NeZero M]
    (hcop : Q.toList.prod.Coprime M) (hM : Squarefree M) (hodd : Odd M) (hM1 : 1 < M)
    (t : ZMod M) (hlift : (Q.toList.prod : ℤ) ∣ (t.val : ℤ) + (M : ℤ) * h₀)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ x, conj (ψ x) = ψ x) (X H : ℝ) (hX : 0 < X)
    (hH : 0 ≤ H) (hcut : H * ((M : ℝ) / X) * Q.toList.prod ≤ N)
    (hsupp : ∀ x : ℝ, H < x → 𝓕 ψ x = 0) :
    ‖∑' n : ℤ, (amplificationWeight Q D n : ℂ) *
        (jacobiSym (n - t.val) M : ℂ) * ψ ((n : ℝ) / X)‖ ≤
      2 * Real.sqrt X *
        ‖originalPositiveFourier Q hQ D M N h₀ ((t.val : ℝ) / M) ((M : ℝ) / X) (𝓕 ψ)‖ := by
  rw [amplified_jacobi_poisson Q hQ D M h₀ hcop hM hodd t hlift ψ X hX,
    norm_mul, norm_mul, jacobiGaussPhase_norm M hM hodd,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hh := originalSignedFourier_norm_le Q hQ D M N h₀ ((t.val : ℝ) / M)
    ((M : ℝ) / X) H (𝓕 ψ) hM1
    (div_pos (by exact_mod_cast NeZero.pos M) hX) hH hcut
    (fourier_real_conj ψ hreal) hsupp
  nlinarith [Real.sqrt_nonneg X]

end Ostmann

end OAI
