import Mathlib.Algebra.BigOperators.Intervals
import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightDivisorEnergy

namespace OAI

/-! # Combining the low and high weights on an actual dyadic kernel segment -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sum_Ioc_dyadic (N : ℕ) (f : ℕ → ℝ) :
    (∑ s ∈ Finset.Ioc N (2 * N), f s) = ∑ n ∈ Finset.range N, f (n + (N + 1)) := by
  rw [← Finset.Ico_succ_succ_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  change (∑ k ∈ Finset.range ((2 * N + 1) - (N + 1)), f ((N + 1) + k)) = _
  have he : (2 * N + 1) - (N + 1) = N := by omega
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  omega

theorem eventual_dyadic_divisor_energy (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → 0 < N → 2 * P.toList.prod ^ 2 ≤ N →
      (2 * N : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → 0 ≤ H →
      (∀ U ⊆ P, ∀ w ∈ W U, 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * U.toList.prod / ((N : ℝ) * v)) →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D W a θ Φ R v U s‖ ^ 2) ≤
        (H * (4 * correlationWeightBudget Φ Φ H H)) * Real.exp (3 * T ^ (9999999 / 10000000 : ℝ) / 250) +
        (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) * Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ)) := by
  classical
  filter_upwards [eventual_high_weight_divisor_energy C₀] with T hT
  intro P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D W a θ Φ R v H c hR hv hH hW hc
  let K := T ^ (9999999 / 10000000 : ℝ)
  let G := fun s => ∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D W a θ Φ R v U s
  let E := fun s : ℕ => (u ^ s.primeFactors.card / (s : ℝ)) * ‖G s‖ ^ 2
  let low := fun s : ℕ => u ^ s.primeFactors.card ≤ Real.exp (K / 200)
  let B := H * (4 * correlationWeightBudget Φ Φ H H)
  have hB : 0 ≤ B := by dsimp [B, correlationWeightBudget]; positivity
  have hlo : (∑ s ∈ S.filter low, E s) ≤ B * Real.exp (3 * K / 250) := by
    have hbase := primeDivisor_quadratic_energy P hP D W a θ Φ R v H (1 / 16) (N + 1) N c
      hR hv hH (by norm_num) (by omega) hN (by omega) hW hc
    have hfull : (∑ s ∈ Finset.Ioc N (2 * N), (1 / (s : ℝ)) * ‖G s‖ ^ 2) ≤
        B * ∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹) := by
      rw [sum_Ioc_dyadic]
      exact hbase
    calc
      _ ≤ ∑ s ∈ S.filter low, Real.exp (K / 200) * ((1 / (s : ℝ)) * ‖G s‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro s hs
        have hh := mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hs).2
          (show 0 ≤ (1 / (s : ℝ)) * ‖G s‖ ^ 2 by positivity)
        convert hh using 1
        dsimp [E]
        ring
      _ ≤ Real.exp (K / 200) * ∑ s ∈ Finset.Ioc N (2 * N), (1 / (s : ℝ)) * ‖G s‖ ^ 2 := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun s hs => hrange s (Finset.mem_filter.mp hs).1) (fun _ _ _ => by positivity)
      _ ≤ Real.exp (K / 200) * (B * ∏ p ∈ P,
          (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) :=
        mul_le_mul_of_nonneg_left hfull (Real.exp_nonneg _)
      _ = B * (Real.exp (K / 200) * ∏ p ∈ P,
          (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (low_weight_euler_bound_scale P hlarge K hcard) hB
  have hhi : (∑ s ∈ S.filter (fun s => ¬low s), E s) ≤
      (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) * Real.exp (-9 * K) := by
    exact hT P hP N (S.filter (fun s => ¬low s)) u hN hsize hcut hcard
      (fun s hs => hS s (Finset.mem_filter.mp hs).1)
      (fun s hs => hrange s (Finset.mem_filter.mp hs).1)
      (fun s hs => hcop s (Finset.mem_filter.mp hs).1) hu huU
      (fun s hs => lt_of_not_ge (Finset.mem_filter.mp hs).2) D W a θ Φ R v H c hR hv hH hW hc
  change (∑ s ∈ S, E s) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S low E]
  exact add_le_add hlo hhi

end Ostmann

end OAI
