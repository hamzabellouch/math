import OAI.NumberTheory.Ostmann.QuadraticCenter.FixedCoefficientMoment
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticArrayApproximation

namespace OAI

/-! # The full small-kernel statistic has a controlled even moment -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_small_kernel_prime_moment (hB : PublishedBonamiBound)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P S R : Finset ℕ) (U Z k l : ℕ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s.primeFactors ⊆ R) →
      (∀ s ∈ S, s ≤ Q.toList.prod ^ 4) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) →
      (∀ s ∈ S, s ≤ U) → (∀ p ∈ P, p ≤ Z) → (S.card : ℝ) ≤ Real.exp (14 * T) →
      1 ≤ Z → Real.exp T ≤ Cpop * T * P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ k → 2 * k ^ 2 ≤ P.card →
      T ^ (3 / 5 : ℝ) / 2 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      1 ≤ l → T ^ (1 / 1000000 : ℝ) / 2 ≤ l → (l : ℝ) ≤ T ^ (1 / 1000000 : ℝ) →
      (U : ℝ) ≤ Real.exp (14 * T) →
      ∀ pick : ℕ → smallKernelParameters T Q.toList.prod,
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖quadraticArrayStatistic S m (fixedQuadraticCoefficient T Q hQ D Φ (pick m))‖ ^ (2 * l)) ≤
        (Real.exp ((103 / 1000 : ℝ) * Q.card) + Real.exp (-10 * T)) ^ (2 * l) := by
  filter_upwards [eventual_fixed_coefficient_moment hB Cpop hCpop H (1 / 1000) Φ hH (by norm_num) hΦ,
    eventual_small_kernel_family_norm 14 H (1 / 1000) Φ (by norm_num) hH (by norm_num) hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hm hn hT
  intro Q hQ D P S R U Z k l hK hQT hlarge hL hS hSR hrange hP hodd hSU hPZ hScard
    hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU pick
  have hU500 : (U : ℝ) ≤ Real.exp (500 * T) :=
    hU.trans (Real.exp_le_exp.mpr (by linarith))
  have huU : ((2 * l : ℕ) : ℝ) ≤ 2 * T ^ (1 / 1000000 : ℝ) := by push_cast; linarith
  have he (i : QuadraticFamilyIndex) (hi : i ∈ smallKernelParameters T Q.toList.prod) :
      Real.sqrt (∑ s ∈ S, (((2 * l : ℕ) : ℝ) ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤ Real.exp ((102 / 1000 : ℝ) * Q.card) := by
    have hh := hn Q hQ U S ((2 * l : ℕ) : ℝ) hK hlarge hU
      (fun s hs => ⟨hS s hs, hSU s hs, hrange s hs⟩) (Nat.cast_nonneg _) huU D i hi
    norm_num only at hh ⊢
    exact hh
  have hh := hm Q hQ D (smallKernelParameters T Q.toList.prod) P S R U Z k l (102 / 1000)
    (smallKernelParameters_subset _ _) hK hQT hlarge hL hS hSR hP hodd hSU hPZ
    hScard hZ hpop hZU hk hsize hkL hkU hl hlL hlU hU500 he pick
  norm_num only at hh ⊢
  exact hh

end Ostmann

end OAI
