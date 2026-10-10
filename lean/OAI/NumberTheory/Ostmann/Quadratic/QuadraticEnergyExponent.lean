import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveDivisorEnergy

namespace OAI

/-! # The numerical .006 exponent after the low/high energy split -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem eventual_quadratic_energy_exponent (A B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      Real.sqrt (A * Real.exp (3 * T ^ (9999999 / 10000000 : ℝ) / 250) +
        B * Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ))) ≤
        Real.exp ((3 / 500 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  have hk := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9999999 / 10000000)).eventually_ge_atTop
    ((A + B) / (2 * ε))
  filter_upwards [hk, eventually_ge_atTop (1 : ℝ)] with T hbound hT
  let K := T ^ (9999999 / 10000000 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hc : A + B ≤ Real.exp (2 * ε * K) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp hbound
    have he := Real.add_one_le_exp (2 * ε * K)
    dsimp [K]
    nlinarith
  have hd : Real.exp (-9 * K) ≤ Real.exp (3 * K / 250) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsum : A * Real.exp (3 * K / 250) + B * Real.exp (-9 * K) ≤
      Real.exp (2 * (3 / 500 + ε) * K) := by
    calc
      _ ≤ (A + B) * Real.exp (3 * K / 250) := by
        have hh := mul_le_mul_of_nonneg_left hd hB
        nlinarith only [hh]
      _ ≤ Real.exp (2 * ε * K) * Real.exp (3 * K / 250) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.sqrt_le_sqrt hsum).trans_eq
  rw [← Real.exp_half]
  congr 1
  ring

theorem eventual_dyadic_positive_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hε : 0 < ε) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      (∀ p ∈ P, 10000 ≤ p) → 0 < N → 2 * P.toList.prod ^ 2 ≤ N →
      (2 * N : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((3 / 500 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  have hnum := eventual_quadratic_energy_exponent
    (H * (4 * correlationWeightBudget Φ Φ H H))
    (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) ε (by positivity) hε
  filter_upwards [eventual_dyadic_positive_energy C₀, hnum] with T hT hn
  intro P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU D a θ R v c hR hv hc
  exact (Real.sqrt_le_sqrt (hT P hP N S u hlarge hN hsize hcut hcard hS hrange hcop hu huU
    D a θ Φ R v H c hR hv hH hΦ hc)).trans hn

end Ostmann

end OAI
