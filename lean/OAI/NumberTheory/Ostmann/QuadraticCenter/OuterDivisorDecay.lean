import OAI.NumberTheory.Ostmann.QuadraticCenter.OuterDivisorNorm

namespace OAI

/-! # Exponential decay of all nontrivial sampled outer divisors -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem outer_divisor_factor_decay (T C mass : ℝ) (L K P : ℕ)
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hmass : 0 ≤ mass)
    (hL : (L : ℝ) ≤ Real.exp (T / 25)) (hK : (K : ℝ) ≤ T)
    (hP : Real.exp T ≤ P) (hCbound : C ≤ Real.exp (T / 100))
    (hmassbound : mass ≤ Real.exp (T / 1000)) :
    (Real.sqrt L * C * (1 + 1 / 16 : ℝ) ^ K / P) * mass ≤ Real.exp (-9 * T / 10) := by
  have hsqrt : Real.sqrt L ≤ Real.exp (T / 50) := by
    apply (Real.sqrt_le_sqrt hL).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  have heuler : (1 + 1 / 16 : ℝ) ^ K ≤ Real.exp (T / 16) := by
    have hbase : (1 + 1 / 16 : ℝ) ≤ Real.exp (1 / 16) := by linarith [Real.add_one_le_exp (1 / 16 : ℝ)]
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 + 1 / 16) hbase K
    rw [← Real.exp_nat_mul] at hp
    exact hp.trans (Real.exp_le_exp.mpr (by linarith))
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le (Real.exp_pos _) hP
  calc
    _ ≤ (Real.exp (T / 50) * Real.exp (T / 100) * Real.exp (T / 16) / Real.exp T) *
        Real.exp (T / 1000) := by gcongr
    _ = Real.exp (T / 50 + T / 100 + T / 16 - T + T / 1000) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventual_outer_divisor_norm_decay (C₀ H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M P : ℕ) (S : Finset ℕ) (u : ℝ),
      (M : ℝ) ≤ Real.exp (C₀ * T) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 25) → Real.exp T ≤ P →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) → 0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ Q.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ Q.powerset, c U * primeDivisorMultiples Q hQ D a θ Φ R v P U s‖ ^ 2) ≤
        Real.exp (-9 * T / 10) := by
  let C := SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [squarefree_coefficient_budget C₀ (1 / 500) (by norm_num),
    eventually_ge_atTop (100 * C), eventually_ge_atTop (1 : ℝ)] with T hbudget hTC hT
  intro Q hQ M P S u hM hcard hL hP hS hu huU D a θ R v c hR hv hc
  have hT0 : 0 ≤ T := by linarith
  have hκ : T ^ (9999999 / 10000000 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (9999999 / 10000000 : ℝ) ≤ 1 by norm_num)
  have hmass := hbudget M S u hM hS hu (show u ≤ 4 * T ^ (1 / 1000000 : ℝ) by
    have hh : 0 ≤ T ^ (1 / 1000000 : ℝ) := Real.rpow_nonneg hT0 _
    linarith)
  have hmassroot : Real.sqrt (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤ Real.exp (T / 1000) := by
    apply (Real.sqrt_le_sqrt hmass).trans
    rw [← Real.exp_half]
    apply Real.exp_le_exp.mpr
    linarith
  have hCbound : C ≤ Real.exp (T / 100) := by linarith [Real.add_one_le_exp (T / 100)]
  have hPpos : 0 < P := by
    have hh : (0 : ℝ) < P := lt_of_lt_of_le (Real.exp_pos _) hP
    exact_mod_cast hh
  apply (primeDivisorMultiples_norm_bound Q hQ D a θ Φ R v H u P S hPpos
    (fun s hs => Nat.pos_of_ne_zero (hS s hs).1.ne_zero) hR hv hH hu hΦ c hc).trans
  have hdecay := outer_divisor_factor_decay T C
    (Real.sqrt (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ))) Q.toList.prod Q.card P
    hT0 hC (Real.sqrt_nonneg _) hL (hcard.trans hκ) hP hCbound hmassroot
  convert hdecay using 1; dsimp [C]; ring

end Ostmann

end OAI
