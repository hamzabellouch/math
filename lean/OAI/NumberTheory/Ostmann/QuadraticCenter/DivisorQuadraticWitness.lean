import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveQuadraticWitness
import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallPositiveQuadratic

namespace OAI

/-! # Inverse witnesses for the genuine divisor density Fourier transforms -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sqrt_two_pow_card (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

theorem small_divisor_coefficient_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (U V : Finset ℕ) (hU : U ⊆ Q) (hV : V ⊆ Q) (s : ℕ)
    (hs : s ≤ Q.toList.prod ^ 4) :
    s * V.toList.prod * U.toList.prod ≤ Q.toList.prod ^ 6 := by
  have hu := primeSet_prod_le_of_subset Q U hQ hU
  have hv := primeSet_prod_le_of_subset Q V hQ hV
  calc
    _ ≤ Q.toList.prod ^ 4 * Q.toList.prod * Q.toList.prod := Nat.mul_le_mul
      (Nat.mul_le_mul hs hv) hu
    _ = _ := by ring

theorem eventual_primeDivisorPositive_phase_witness (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (U V : Finset ℕ) (M h₀ s : ℕ) (θ R K : ℝ),
      U ⊆ Q → V ⊆ Q → 0 < s → s ≤ Q.toList.prod ^ 4 →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      0 ≤ K → K ≤ T ^ (9999999 / 10000000 : ℝ) →
      Real.exp (10 * T) ≤ R → R ≤ Real.exp (14 * T) →
      (Real.sqrt 2) ^ U.card * Real.exp (-K) <
        ‖primeDivisorPositive Q hQ D (divisorQuadraticScalar (quadraticInverseResidue M) V)
          (fun _ => (h₀ : ℝ) + θ) Φ R V.toList.prod U s‖ →
      ∃ c ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊, ∃ b : ℤ,
        |(c : ℝ) * θ - b| ≤ Real.exp (13 * T / 100) / R := by
  filter_upwards [eventual_positiveQuadraticSum_phase_witness B Φ hB hΦ] with T hT
  intro Q hQ D U V M h₀ s θ R K hU hV hs hsL hL hK hKT hRlo hRhi hlarge
  have hu : ∀ p ∈ U, p.Prime := fun p hp => hQ p (hU hp)
  have hv : ∀ p ∈ V, p.Prime := fun p hp => hQ p (hV hp)
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hu)).ne'⟩
  have hVpos : 0 < V.toList.prod := prime_list_prod_pos _ (primeSet_list_prime V hv)
  have hc : ((s * V.toList.prod * U.toList.prod : ℕ) : ℝ) ≤ Real.exp (3 * T / 25) := by
    have hh : ((s * V.toList.prod * U.toList.prod : ℕ) : ℝ) ≤ (Q.toList.prod : ℝ) ^ 6 := by
      exact_mod_cast small_divisor_coefficient_bound Q hQ U V hU hV s hsL
    apply hh.trans
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q.toList.prod : (0 : ℝ) ≤ Q.toList.prod) hL 6
    rw [← Real.exp_nat_mul] at hp
    convert hp using 1
    congr 1
    norm_num
    ring
  simp only [primeDivisorPositive, dite_eq_left hU] at hlarge
  apply hT U.toList.prod s V.toList.prod
    (densityFourier (densityCRTList U.toList (primeSet_list_prime U hu)
      (primeSet_list_coprime U hu) D).value)
    (divisorQuadraticScalar (quadraticInverseResidue M) V U) h₀ θ R K
    (densityCRTList U.toList (primeSet_list_prime U hu) (primeSet_list_coprime U hu) D).fourier_nonunit
    (densityCRTList_energy _ _ _ _) hs hVpos hK hKT hc hRlo hRhi
  simpa only [primeSet_modulus_primeFactors U hu, sqrt_two_pow_card] using hlarge

end Ostmann

end OAI
