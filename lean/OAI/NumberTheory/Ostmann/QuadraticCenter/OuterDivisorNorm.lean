import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMultiples

namespace OAI

/-! # The outer divisor gives the full reciprocal-divisor norm gain -/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def primeDivisorMultiples (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (P : ℕ) (U : Finset ℕ) (s : ℕ) : ℂ :=
  (P : ℂ)⁻¹ * primeDivisorPositive Q hQ D a θ Φ R v U (s * P ^ 2)

theorem primeDivisorMultiples_combination_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s P : ℕ)
    (hP : 0 < P) (hs : 0 < s) (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    ‖∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s‖ ≤
      (Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P := by
  have he : (∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s) =
      (P : ℂ)⁻¹ * ∑ U ∈ Q.powerset, c U * primeDivisorPositive Q hQ D a θ Φ R v U (s * P ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    unfold primeDivisorMultiples
    ring
  rw [he, norm_mul, norm_inv, Complex.norm_natCast]
  have hp := primeDivisorPositive_combination_uniform_bound Q hQ D a θ Φ R v H (s * P ^ 2)
    hR hv hH (Nat.mul_pos hs (pow_pos hP _)) hΦ c hc
  apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg P))).trans_eq
  ring

theorem primeDivisorMultiples_norm_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H u : ℝ) (P : ℕ) (S : Finset ℕ)
    (hP : 0 < P) (hS : ∀ s ∈ S, 0 < s) (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hu : 0 ≤ u)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) (c : Finset ℕ → ℂ)
    (hc : ∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) :
    Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
      ‖∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s‖ ^ 2) ≤
      ((Real.sqrt Q.toList.prod * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H) *
        (1 + 1 / 16 : ℝ) ^ Q.card / P) *
          Real.sqrt (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) := by
  apply sqrt_weighted_energy_le_uniform
  · positivity
  · intro s _; positivity
  · intro s hs
    exact primeDivisorMultiples_combination_bound Q hQ D a θ Φ R v H s P hP (hS s hs)
      hR hv hH hΦ c hc

end Ostmann

end OAI
