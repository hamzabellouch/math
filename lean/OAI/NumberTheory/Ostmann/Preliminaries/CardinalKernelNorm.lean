import OAI.NumberTheory.Ostmann.QuadraticCenter.IntegerKernelScale
import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallKernelScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.OffWitnessEnergy

namespace OAI

/-! # Coefficient norms at the actual cardinality of the selected primes -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

private theorem kernelScale_range (C₀ T K : ℝ) (M : ℕ)
    (hC₀ : 0 ≤ C₀) (hT : 1 ≤ T)
    (hK : T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K)
    (hM : (M : ℝ) ≤ Real.exp (C₀ * T)) :
    (M : ℝ) ≤ Real.exp ((1000000 * C₀) * integerKernelScale K) := by
  apply hM.trans
  apply Real.exp_le_exp.mpr
  have hlo := integerKernelScale_lower T K hT hK
  nlinarith

/-- The large-kernel norm has exponent `.006 K`, with `K` the actual
number of selected primes, including when `K` is a small fixed multiple
of the original analytic scale. -/
theorem eventual_large_kernel_norm_card (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (P.card : ℝ) →
      (∀ p ∈ P, 10000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, 4 * P.toList.prod ^ 2 ≤ s ∧ s ≤ M) →
      (∀ s ∈ S, P.toList.prod.Coprime s) →
      2 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((3 / 500 + ε) * P.card) := by
  have hevent := eventual_large_kernel_positive_norm (1000000 * C₀) H ε Φ
    (by positivity) hH hε hΦ
  filter_upwards [eventually_at_integerKernelScale _ hevent,
    eventually_ge_atTop (1 : ℝ)] with T hnorm hT
  intro P hP M S u hK hlarge hM hS hrange hcop hu huU D a θ R v c hR hv hc
  have hscale := integerKernelScale_power (P.card : ℝ) (by positivity)
  have hn := hnorm (P.card : ℝ) hK P hP M S u hlarge
    (kernelScale_range C₀ T P.card M hC₀ hT hK hM) hscale.ge hS hrange hcop hu
    (integerKernelScale_moment T P.card u hT hK huU) D a θ R v c hR hv hc
  simpa only [hscale] using hn

theorem eventual_small_kernel_norm_card (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (P.card : ℝ) →
      (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M ∧ s ≤ P.toList.prod ^ 4) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      (P.toList.prod : ℝ) ^ 6 ≤ R → 0 < v → v ≤ P.toList.prod →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((1 / 10 + ε) * P.card) := by
  have hevent := eventual_small_kernel_norm_from_ranges (1000000 * C₀) H ε Φ hH hε hΦ
  filter_upwards [eventually_at_integerKernelScale _ hevent,
    eventually_ge_atTop (1 : ℝ)] with T hnorm hT
  intro P hP M S u hK hM hS hu huU D a θ R v c hR hv hvL hc
  have hscale := integerKernelScale_power (P.card : ℝ) (by positivity)
  have hn := hnorm (P.card : ℝ) hK P hP M S u
    (kernelScale_range C₀ T P.card M hC₀ hT hK hM) hscale.ge hS hu
    (integerKernelScale_moment T P.card u hT hK huU) D a θ R v c hR hv hvL hc
  simpa only [hscale] using hn

theorem eventual_off_witness_norm_card (C₀ ε : ℝ) (hC₀ : 0 ≤ C₀) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (P.card : ℝ) →
      (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (c : Finset ℕ → ℂ) (G : Finset ℕ → ℕ → ℂ),
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ s ∈ S, ∀ U ∈ P.powerset,
        ‖G U s‖ ≤ Real.exp (-9 * P.card / 10) * (Real.sqrt 2) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * G U s‖ ^ 2) ≤
        Real.exp ((-4 / 5 + ε) * P.card) := by
  have hevent := eventual_off_witness_norm (1000000 * C₀) ε hε
  filter_upwards [eventually_at_integerKernelScale _ hevent,
    eventually_ge_atTop (1 : ℝ)] with T hnorm hT
  intro P M S u hK hM hS hu huU c G hc hG
  have hscale := integerKernelScale_power (P.card : ℝ) (by positivity)
  have hn := hnorm (P.card : ℝ) hK P M S u
    (kernelScale_range C₀ T P.card M hC₀ hT hK hM) hscale.ge hS hu
    (integerKernelScale_moment T P.card u hT hK huU) c G hc (by simpa only [hscale] using hG)
  simpa only [hscale] using hn

end Ostmann

end OAI
