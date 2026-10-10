import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCompactCutoff
import OAI.NumberTheory.Ostmann.QuadraticCenter.DyadicDivisorEnergy

namespace OAI

/-! # Energy of the original positive quadratic series on a dyadic segment -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def primeDivisorPositive (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (U : Finset ℕ) (s : ℕ) : ℂ := by
  classical
  exact if hU : U ⊆ P then
    let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hP p (hU hp)))).ne'⟩
    positiveQuadraticSum (densityFourier (densityCRTList U.toList
      (primeSet_list_prime U (fun p hp => hP p (hU hp)))
      (primeSet_list_coprime U (fun p hp => hP p (hU hp))) D).value)
      (a U) (θ U) Φ R v s
  else 0

theorem primeDivisorPositive_eq_cutoff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (N s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hN : 0 < N) (hs : N ≤ s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (U : Finset ℕ) :
    primeDivisorPositive P hP D a θ Φ R v U s =
      primeDivisorQuadratic P hP D (fun U => quadraticCompactCutoff U.toList.prod R v H N)
        a θ Φ R v U s := by
  classical
  by_cases hU : U ⊆ P
  · let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
      (primeSet_list_prime U (fun p hp => hP p (hU hp)))).ne'⟩
    simp only [primeDivisorPositive, primeDivisorQuadratic, dite_eq_left hU, primeSetQuadraticSum]
    exact positiveQuadraticSum_eq_cutoff _ _ _ _ _ _ _ _ _ hR hv hN hs hΦ
  · simp only [primeDivisorPositive, primeDivisorQuadratic, dite_eq_right hU]

theorem eventual_dyadic_positive_energy (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → 0 < N → 2 * P.toList.prod ^ 2 ≤ N →
      (2 * N : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → 0 ≤ H → (∀ x : ℝ, H < x → Φ x = 0) →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        (H * (4 * correlationWeightBudget Φ Φ H H)) * Real.exp (3 * T ^ (9999999 / 10000000 : ℝ) / 250) +
        (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) * Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_dyadic_divisor_energy C₀] with T hT
  intro P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D a θ Φ R v H c
    hR hv hH hΦ hc
  have he (s : ℕ) (hs : s ∈ S) (U : Finset ℕ) :
      primeDivisorPositive P hP D a θ Φ R v U s =
      primeDivisorQuadratic P hP D (fun U => quadraticCompactCutoff U.toList.prod R v H N)
        a θ Φ R v U s :=
    primeDivisorPositive_eq_cutoff P hP D a θ Φ R v H N s hR hv hN
      (Finset.mem_Ioc.mp (hrange s hs)).1.le hΦ U
  have heSum : (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) =
      ∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D
        (fun U => quadraticCompactCutoff U.toList.prod R v H N) a θ Φ R v U s‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [he s hs]
  rw [heSum]
  apply hT P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D
    (fun U => quadraticCompactCutoff U.toList.prod R v H N) a θ Φ R v H c hR hv hH _ hc
  intro U _
  exact quadraticCompactCutoff_spec U.toList.prod R v H N hR.le hv.le hH

end Ostmann

end OAI
