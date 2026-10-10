import OAI.NumberTheory.Ostmann.QuadraticCenter.DivisorWeightedCoefficient
import OAI.NumberTheory.Ostmann.Preliminaries.CardinalKernelNorm
import OAI.NumberTheory.Ostmann.QuadraticCenter.OuterDivisorDecay

namespace OAI

/-! # Both divisor sums in the original quadratic coefficient -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

/-- The v divisor is part of the original modular quadratic argument. -/
noncomputable def divisorQuadraticScalar
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (V U : Finset ℕ) : ZMod U.toList.prod :=
  a U * (V.toList.prod : ZMod U.toList.prod)

theorem divisorQuadraticScalar_congr_point
    (a b : ∀ U : Finset ℕ, ZMod U.toList.prod) (V U : Finset ℕ) (h : a U = b U) :
    divisorQuadraticScalar a V U = divisorQuadraticScalar b V U := by
  exact congrArg (fun x : ZMod U.toList.prod => x * (V.toList.prod : ZMod U.toList.prod)) h

noncomputable def fullQuadraticCoefficient (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (P : ℕ) (c ξ : Finset ℕ → ℂ) (s : ℕ) : ℂ :=
  divisorWeightedCoefficient Q ξ (fun V s =>
    ∑ U ∈ Q.powerset, c U *
      primeDivisorMultiples Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod P U s) s

theorem fullQuadraticCoefficient_one (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : ∀ p : ℕ, Finset (ZMod p))
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R : ℝ) (c ξ : Finset ℕ → ℂ) (s : ℕ) :
    fullQuadraticCoefficient Q hQ D a θ Φ R 1 c ξ s =
      divisorWeightedCoefficient Q ξ (fun V s => ∑ U ∈ Q.powerset, c U *
        primeDivisorPositive Q hQ D (divisorQuadraticScalar a V) θ Φ R V.toList.prod U s) s := by
  simp only [fullQuadraticCoefficient, primeDivisorMultiples, one_pow, mul_one,
    Nat.cast_one, inv_one, one_mul]

theorem eventual_full_large_kernel_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, 4 * Q.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, Q.toList.prod.Coprime s) →
      2 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R : ℝ) (c ξ : Finset ℕ → ℂ),
      0 < R → (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fullQuadraticCoefficient Q hQ D a θ Φ R 1 c ξ s‖ ^ 2) ≤
        Real.exp ((7 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_large_kernel_norm_card C₀ H ε Φ hC₀ hH hε hΦ] with T hn
  intro Q hQ M S u hK hlarge hM hS hrange hcop hu huU D a θ R c ξ hR hc hξ
  simp_rw [fullQuadraticCoefficient_one]
  refine (divisorWeightedCoefficient_energy_exp_le Q ξ _ S _
    (Real.exp ((3 / 500 + ε) * Q.card)) hlarge (fun _ _ => by positivity)
    (Real.exp_nonneg _) hξ ?_).trans_eq ?_
  · intro V hV
    have hVQ := Finset.mem_powerset.mp hV
    have hv : 0 < V.toList.prod := prime_list_prod_pos _
      (primeSet_list_prime V (fun p hp => hQ p (hVQ hp)))
    exact hn Q hQ M S u hK (fun p hp => by have := hlarge p hp; omega)
      hM hS hrange hcop hu huU D (divisorQuadraticScalar a V) θ R V.toList.prod c hR (by exact_mod_cast hv) hc
  · rw [← Real.exp_add]
    congr 1
    ring

theorem eventual_full_small_kernel_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M ∧ s ≤ Q.toList.prod ^ 4) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R : ℝ) (c ξ : Finset ℕ → ℂ),
      (Q.toList.prod : ℝ) ^ 6 ≤ R →
      (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fullQuadraticCoefficient Q hQ D a θ Φ R 1 c ξ s‖ ^ 2) ≤
        Real.exp ((101 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_small_kernel_norm_card C₀ H ε Φ hC₀ hH hε hΦ] with T hn
  intro Q hQ M S u hK hlarge hM hS hu huU D a θ R c ξ hR hc hξ
  simp_rw [fullQuadraticCoefficient_one]
  refine (divisorWeightedCoefficient_energy_exp_le Q ξ _ S _
    (Real.exp ((1 / 10 + ε) * Q.card)) hlarge (fun _ _ => by positivity)
    (Real.exp_nonneg _) hξ ?_).trans_eq ?_
  · intro V hV
    have hVQ := Finset.mem_powerset.mp hV
    have hv : 0 < V.toList.prod := prime_list_prod_pos _
      (primeSet_list_prime V (fun p hp => hQ p (hVQ hp)))
    have hvL := primeSet_prod_le_of_subset Q V hQ hVQ
    exact hn Q hQ M S u hK hM hS hu huU D (divisorQuadraticScalar a V) θ R V.toList.prod c hR
      (by exact_mod_cast hv) (by exact_mod_cast hvL) hc
  · rw [← Real.exp_add]
    congr 1
    ring

theorem eventual_full_outer_divisor_decay (C₀ H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M P : ℕ) (S : Finset ℕ) (u : ℝ),
      (M : ℝ) ≤ Real.exp (C₀ * T) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) → Real.exp T ≤ P →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) → 0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R : ℝ) (c ξ : Finset ℕ → ℂ),
      0 < R → (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ V ∈ Q.powerset, ‖ξ V‖ ≤ 1) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fullQuadraticCoefficient Q hQ D a θ Φ R P c ξ s‖ ^ 2) ≤
        Real.exp (-4 * T / 5) := by
  filter_upwards [eventual_outer_divisor_norm_decay C₀ H Φ hH hΦ,
    eventually_ge_atTop (1 : ℝ)] with T hn hT
  intro Q hQ M P S u hM hK hlarge hL hP hS hu huU D a θ R c ξ hR hc hξ
  have hKT : (Q.card : ℝ) ≤ T := hK.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num))
  refine (divisorWeightedCoefficient_energy_exp_le Q ξ _ S _
    (Real.exp (-9 * T / 10)) hlarge (fun _ _ => by positivity)
    (Real.exp_nonneg _) hξ ?_).trans ?_
  · intro V hV
    have hVQ := Finset.mem_powerset.mp hV
    have hv : 0 < V.toList.prod := prime_list_prod_pos _
      (primeSet_list_prime V (fun p hp => hQ p (hVQ hp)))
    exact hn Q hQ M P S u hM hK hL hP hS hu huU D (divisorQuadraticScalar a V) θ R V.toList.prod c hR
      (by exact_mod_cast hv) hc
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

end Ostmann

end OAI
