import OAI.NumberTheory.Ostmann.QuadraticCenter.SignedQuadraticFrequency
import OAI.NumberTheory.Ostmann.Construction.OriginalFourierCoefficients

namespace OAI

/-! # The positive half of the original signed Fourier expression -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def primeDivisorSignedFrequency (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (M h₀ : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  if hU : U ⊆ Q then
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    (Real.sqrt (R * U.toList.prod) : ℂ)⁻¹ * ∑' u : ℤ,
      integerQuadraticFrequency (densityFourier (primeDivisorDensity Q hQ D U))
        (quadraticInverseResidue M U) ((h₀ : ℝ) + θ) Φ R M u
  else 0

noncomputable def originalSignedFourier (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ U ∈ Q.powerset, quadraticSymbolCoefficient M U *
    primeDivisorSignedFrequency Q hQ D U M h₀ θ R Φ

theorem primeDivisorSignedFrequency_split (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (M N h₀ : ℕ) (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hM : 1 < M) (hR : 0 < R) (hcut : H * R * U.toList.prod ≤ N)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    primeDivisorSignedFrequency Q hQ D U M h₀ θ R Φ =
      primeDivisorFrequency Q hQ D U M N h₀ θ R Φ +
      (jacobiSym (-1) M : ℂ) * conj (primeDivisorFrequency Q hQ D U M N h₀ θ R Φ) := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  have he := integerQuadraticFrequency_split
    (densityFourier (primeDivisorDensity Q hQ D U)) (quadraticInverseResidue M U)
    ((h₀ : ℝ) + θ) Φ R H M N hM hR
    (densityFourier_conj _ (primeDivisorDensity_conj Q hQ D U hU)) hΦ hcut hsupp
  simp only [primeDivisorSignedFrequency, primeDivisorFrequency, dite_eq_left hU]
  rw [he]
  simp only [primeDivisorDensity, dite_eq_left hU, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem quadraticSymbolCoefficient_conj (M : ℕ) (U : Finset ℕ) :
    conj (quadraticSymbolCoefficient M U) = quadraticSymbolCoefficient M U := by
  simp only [quadraticSymbolCoefficient, map_mul, map_pow, Complex.conj_ofReal]

/-- The entire divisor sum has a common conjugation sign. Thus the positive
half controls the signed expression before any absolute values are distributed. -/
theorem originalSignedFourier_split (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ)
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hM : 1 < M) (hR : 0 < R) (hH : 0 ≤ H)
    (hcut : H * R * Q.toList.prod ≤ N)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    originalSignedFourier Q hQ D M h₀ θ R Φ =
      originalPositiveFourier Q hQ D M N h₀ θ R Φ +
      (jacobiSym (-1) M : ℂ) * conj (originalPositiveFourier Q hQ D M N h₀ θ R Φ) := by
  unfold originalSignedFourier originalPositiveFourier
  simp only [map_sum, map_mul, quadraticSymbolCoefficient_conj]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro U hU
  have hsub := Finset.mem_powerset.mp hU
  have hcutU := (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (primeSet_prod_le_of_subset Q U hQ hsub)) (mul_nonneg hH hR.le)).trans hcut
  rw [primeDivisorSignedFrequency_split Q hQ D U hsub M N h₀ θ R H Φ
    hM hR hcutU hΦ hsupp]
  ring

theorem originalSignedFourier_norm_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N h₀ : ℕ)
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hM : 1 < M) (hR : 0 < R) (hH : 0 ≤ H)
    (hcut : H * R * Q.toList.prod ≤ N)
    (hΦ : ∀ x, Φ (-x) = conj (Φ x)) (hsupp : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖originalSignedFourier Q hQ D M h₀ θ R Φ‖ ≤
      2 * ‖originalPositiveFourier Q hQ D M N h₀ θ R Φ‖ := by
  rw [originalSignedFourier_split Q hQ D M N h₀ θ R H Φ hM hR hH hcut hΦ hsupp]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_conj]
  have hc : ‖(jacobiSym (-1) M : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy (-1) M with h | h | h <;> rw [h] <;> norm_num
  nlinarith [norm_nonneg (originalPositiveFourier Q hQ D M N h₀ θ R Φ)]

end Ostmann

end OAI
