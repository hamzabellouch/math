import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeParameters
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.HarmonicBlockBound

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySmoothDampedFamily
open Finset OrdinaryCorrelations SourcePrimeFactor Filter OrdinaryArchimedeanTwist

theorem uniform_smooth_harmonic_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ (P S : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, |t| ≤ (M:ℝ)^k/2 →
        ‖∑ n ∈ Ioc M (2*M), (n:ℂ)⁻¹ * twist (smoothDamped f P S z) t n‖ ≤ ε := by
  have hh := uniform_smooth_power_bound hf hm hNP k hk (show 0 < ε/6 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  filter_upwards [eventually_ge_atTop (max N 1)] with M hM
  have hM0 : 0 < M := by omega
  intro P S hP z hz t ht
  have hb := OrdinaryDyadicHarmonic.harmonic_interval_bound
    (twist (smoothDamped f P S z) t) hM0 (show 0 ≤ ε/6 by positivity)
    (by
      intro L hML hL2
      have hL0 : 0 < L := by omega
      have hLr : (0:ℝ) < L := by exact_mod_cast hL0
      have hMLr : (M:ℝ) ≤ L := by exact_mod_cast hML
      have hp : (M:ℝ)^k ≤ (L:ℝ)^k := pow_le_pow_left₀ (Nat.cast_nonneg M) hMLr k
      have hb := hN L (by omega) P S hP z hz t (by linarith)
      rw [norm_mul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul] at hb
      exact (div_le_iff₀ hLr).mp hb)
  nlinarith

theorem uniform_smooth_harmonic_segment_bound {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, ∀ L : ℕ, M ≤ L → L ≤ 2*M → ∀ (P S : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, |t| ≤ (M:ℝ)^k/2 →
        ‖∑ n ∈ Ioc M L, (n:ℂ)⁻¹ * twist (smoothDamped f P S z) t n‖ ≤ ε := by
  have hh := uniform_smooth_power_bound hf hm hNP k hk (show 0 < ε/6 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  filter_upwards [eventually_ge_atTop (max N 1)] with M hM
  have hM0 : 0 < M := by omega
  intro L hML hL P S hP z hz t ht
  have hb := OrdinaryDyadicHarmonic.harmonic_segment_bound
    (twist (smoothDamped f P S z) t) hM0 hML hL (show 0 ≤ ε/6 by positivity)
    (by
      intro L hML hL2
      have hL0 : 0 < L := by omega
      have hLr : (0:ℝ) < L := by exact_mod_cast hL0
      have hMLr : (M:ℝ) ≤ L := by exact_mod_cast hML
      have hp : (M:ℝ)^k ≤ (L:ℝ)^k := pow_le_pow_left₀ (Nat.cast_nonneg M) hMLr k
      have hb := hN L (by omega) P S hP z hz t (by linarith)
      rw [norm_mul, norm_inv, Complex.norm_natCast, ← div_eq_inv_mul] at hb
      exact (div_le_iff₀ hLr).mp hb)
  nlinarith

end OrdinarySmoothDampedFamily

end

end OAI
