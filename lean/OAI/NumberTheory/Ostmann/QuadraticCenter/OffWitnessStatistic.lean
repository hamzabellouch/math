import OAI.NumberTheory.Ostmann.QuadraticCenter.OffWitnessMoment
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticArrayApproximation

namespace OAI

/-! # Mean absolute size of the fixed off-witness Jacobi statistic -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_off_witness_prime_mean (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P S R : Finset ℕ) (U Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (14 * T) →
      ∀ pick : ℕ → offWitnessParameters T Q hQ D Φ S,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, rootNormalizedCoefficient (fixedQuadraticCoefficient T Q hQ D Φ (pick m)) s *
            (realJacobi s.val m : ℂ)‖) ≤
        Real.exp ((-797 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T) := by
  filter_upwards [eventual_off_witness_prime_moment hB Cpop hCpop H Φ hH hΦ] with T hm
  intro Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  have hh := hm Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  exact quadraticArrayStatistic_mean_of_moment P S k l
    (fun i : offWitnessParameters T Q hQ D Φ S => fixedQuadraticCoefficient T Q hQ D Φ i)
    pick _ hP hl (by positivity) hh

end Ostmann

end OAI
