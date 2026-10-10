import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetDivisorSum
import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiComplex
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticQuadraticCoefficient

namespace OAI

/-! # The original density Fourier frequencies as divisor quadratic sums -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def primeDivisorFrequency (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (M N h₀ : ℕ)
    (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) : ℂ := by
  classical
  exact if hU : U ⊆ Q then
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    (Real.sqrt (R * U.toList.prod) : ℂ)⁻¹ *
      ∑ u ∈ Finset.Icc 1 N, (realJacobi u M : ℂ) *
        quadraticFrequencyTerm (densityFourier (densityCRTList U.toList
          (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
          (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value)
          (quadraticInverseResidue M U) ((h₀ : ℝ) + θ) Φ R u
  else 0

theorem primeDivisorMultiples_eq_original (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U V : Finset ℕ) (hU : U ⊆ Q)
    (M h₀ s P : ℕ) (θ R : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R)
    (hV : 0 < V.toList.prod) (hP : 0 < P) :
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
    primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
      (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s =
      positiveQuadraticMultiples (densityFourier (densityCRTList U.toList
        (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
        (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value)
        (quadraticInverseResidue M U * (V.toList.prod : ZMod U.toList.prod))
        ((h₀ : ℝ) + θ) Φ R V.toList.prod s P := by
  intro _
  rw [positiveQuadraticMultiples_eq _ _ _ _ _ _ _ _ hP hR.le (by exact_mod_cast hV.le)]
  simp only [primeDivisorMultiples, primeDivisorPositive, dite_eq_left hU, divisorQuadraticScalar]

theorem primeDivisorFrequency_expansion (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U : Finset ℕ) (hU : U ⊆ Q)
    (M N h₀ : ℕ) [NeZero M] (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hR : 0 < R) (hH : 0 ≤ H) (hN : 1 ≤ N)
    (hcut : H * R * Q.toList.prod ≤ N) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    primeDivisorFrequency Q hQ D U M N h₀ θ R Φ =
      ∑ P ∈ M.divisors, (ArithmeticFunction.moebius P : ℂ) *
        ∑ s ∈ squarefreeKernelSupport Q.toList.prod N,
          ((realJacobi s M : ℂ) * (Real.sqrt (s : ℝ) : ℂ)⁻¹) *
          ∑ V ∈ Q.powerset,
            ((realJacobi V.toList.prod M : ℂ) * (Real.sqrt (V.toList.prod : ℝ) : ℂ)⁻¹) *
            primeDivisorMultiples Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
              (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod P U s := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  have hcutU : H * R * U.toList.prod ≤ N := by
    exact (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (primeSet_prod_le_of_subset Q U hQ hU)) (mul_nonneg hH hR.le)).trans hcut
  have he := quadratic_frequency_expansion Q.toList.prod N (primeSet_modulus_squarefree Q hQ)
    (NeZero.pos M) (jacobiComplex M) (jacobiComplex_isQuadratic M)
    (densityFourier (densityCRTList U.toList (primeSet_list_prime U (fun p hp => hQ p (hU hp)))
      (primeSet_list_coprime U (fun p hp => hQ p (hU hp))) D).value)
    (quadraticInverseResidue M U) ((h₀ : ℝ) + θ) R H Φ hR hH hN hcutU hΦ
  simp only [jacobiComplex_natCast] at he
  simp only [primeDivisorFrequency, dite_eq_left hU]
  rw [he]
  apply Finset.sum_congr rfl
  intro P hP
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [sum_primeSet_divisors Q hQ]
  apply Finset.sum_congr rfl
  intro V hV
  congr 1
  exact (primeDivisorMultiples_eq_original Q hQ D U V hU M h₀ s P θ R Φ hR
    (prime_list_prod_pos _ (primeSet_list_prime V (fun p hp => hQ p ((Finset.mem_powerset.mp hV) hp))))
    (Nat.pos_of_mem_divisors hP)).symm

end Ostmann

end OAI
