import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightQuadraticWaves

namespace OAI

/-! # High-weight correlation of the original prime-divisor quadratic sums -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem eventual_high_weight_primeSet_correlation (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (U V : Finset ℕ)
      (hpU : ∀ p ∈ U, p.Prime) (hpV : ∀ p ∈ V, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < N → 2 * (U ∪ V).toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, (U ∪ V).toList.prod.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (W W' : Finset ℕ)
        (a : ZMod U.toList.prod) (b : ZMod V.toList.prod)
        (Φ Ψ : 𝓢(ℝ, ℂ)) (θ η R v H : ℝ),
      0 < R → 0 < v → 0 ≤ H →
      (∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * U.toList.prod / ((N : ℝ) * v)) →
      (∀ w ∈ W', 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * V.toList.prod / ((N : ℝ) * v)) →
      ‖∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
        (primeSetQuadraticSum U hpU D W a θ Φ R v s *
          conj (primeSetQuadraticSum V hpV D W' b η Ψ R v s) / (s : ℂ))‖ ≤
        H * (SchwartzMap.seminorm ℝ 0 0 Φ * SchwartzMap.seminorm ℝ 0 0 Ψ) *
          Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_high_weight_quadratic_waves C₀] with T hT
  intro U V hpU hpV N S u hN hsize hcut hS hrange hcop hu huU hhigh D W W' a b
    Φ Ψ θ η R v H hR hv hH hW hW'
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime U hpU)).ne'⟩
  let : NeZero V.toList.prod := ⟨(prime_list_prod_pos _ (primeSet_list_prime V hpV)).ne'⟩
  have heU (s : ℕ) := primeSetQuadraticSum_eq_unit_waves U hpU D W a θ Φ R v s
    (fun w hw => (hW w hw).1) hR hv
  have heV (s : ℕ) := primeSetQuadraticSum_eq_unit_waves V hpV D W' b η Ψ R v s
    (fun w hw => (hW' w hw).1) hR hv
  simp_rw [heU, heV]
  apply hT U V hpU hpV N S u hN hsize hcut hS hrange hcop hu huU hhigh D
    (unitQuadraticSupport W a) (unitQuadraticSupport W' b)
    (quadraticUnitScalar a) (quadraticUnitScalar b) Φ Ψ
    (fun w => θ * v * (w : ℝ) ^ 2 / U.toList.prod)
    (fun w => R * U.toList.prod / (v * (w : ℝ) ^ 2))
    (fun w => η * v * (w : ℝ) ^ 2 / V.toList.prod)
    (fun w => R * V.toList.prod / (v * (w : ℝ) ^ 2)) R v H hR hv
  exact quadratic_support_pair_count _ _ R U.toList.prod V.toList.prod v N H hR
    (by exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime U hpU)) hv
    (by exact_mod_cast hN) hH
    (fun w hw => hW w (unitQuadraticSupport_subset W a hw))
    (fun w hw => hW' w (unitQuadraticSupport_subset W' b hw))

end Ostmann

end OAI
