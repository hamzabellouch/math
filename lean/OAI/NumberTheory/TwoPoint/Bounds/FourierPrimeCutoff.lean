import OAI.NumberTheory.TwoPoint.Bounds.FinitePrimePhases
import OAI.NumberTheory.TwoPoint.Bounds.WeightedFourierIntegration
import Mathlib.Analysis.Fourier.Inversion

namespace OAI

/-! Fourier inversion of a cutoff evaluated at the centered count of
distinct prime divisors. The integral kernel splits into a constant phase
and the multiplicative finite-prime twist. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical FourierTransform

noncomputable def primeCutoffKernel (P : Finset ℕ) (μ σ t : ℝ) (n : ℕ) : ℂ :=
  additiveCharacter (-t * μ / σ) 1 * finitePrimePhase P (t / σ) n

lemma norm_primeCutoffKernel (P : Finset ℕ) (μ σ t : ℝ) (n : ℕ) :
    ‖primeCutoffKernel P μ σ t n‖ = 1 := by
  simp only [primeCutoffKernel, norm_mul, norm_additiveCharacter,
    norm_finitePrimePhase, one_mul]

lemma primeCutoffKernel_eq_exp (P : Finset ℕ) (μ σ t : ℝ) (n : ℕ) :
    primeCutoffKernel P μ σ t n =
      Complex.exp (((2 * Real.pi * t *
        (((finitePrimeDivisorCount P n : ℝ) - μ) / σ) : ℝ) : ℂ) * Complex.I) := by
  unfold primeCutoffKernel finitePrimePhase additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma continuous_primeCutoffKernel (P : Finset ℕ) (μ σ : ℝ) (n : ℕ) :
    Continuous (fun t => primeCutoffKernel P μ σ t n) := by
  simp_rw [primeCutoffKernel_eq_exp]
  fun_prop

lemma integrable_weighted_primeCutoffKernel (P : Finset ℕ) (μ σ : ℝ) (n : ℕ)
    {w : ℝ → ℂ} (hw : Integrable w) :
    Integrable (fun t => w t * primeCutoffKernel P μ σ t n) := by
  exact hw.mul_bdd (continuous_primeCutoffKernel P μ σ n).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => (norm_primeCutoffKernel P μ σ t n).le))

noncomputable def primeCountCutoff (P : Finset ℕ) (μ σ : ℝ)
    (w : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ t, w t * primeCutoffKernel P μ σ t n

lemma primeCountCutoff_eq_fourierInv (P : Finset ℕ) (μ σ : ℝ)
    (w : ℝ → ℂ) (n : ℕ) :
    primeCountCutoff P μ σ w n =
      𝓕⁻ w (((finitePrimeDivisorCount P n : ℝ) - μ) / σ) := by
  rw [Real.fourierInv_eq']
  unfold primeCountCutoff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    rw [primeCutoffKernel_eq_exp]
    simp only [smul_eq_mul, Real.inner_apply, mul_assoc]
    exact mul_comm _ _)

/-- This is the actual cutoff `φ((ω_P(n)-μ)/σ)` when the frequency
coefficient is the Fourier transform of a continuous integrable cutoff. -/
theorem primeCountCutoff_fourier (P : Finset ℕ) (μ σ : ℝ)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (hi : Integrable φ)
    (hFourier : Integrable (𝓕 φ)) (n : ℕ) :
    primeCountCutoff P μ σ (𝓕 φ) n =
      φ (((finitePrimeDivisorCount P n : ℝ) - μ) / σ) := by
  rw [primeCountCutoff_eq_fourierInv, hφ.fourierInv_fourier_eq hi hFourier]

/-- Exact interchange for the two prime-count cutoffs in a finite
correlation sum. -/
theorem primeCountCutoff_pair_sum {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n m : ι → ℕ) (P Q : Finset ℕ) (μ σ ν τ : ℝ) (w₁ w₂ : ℝ → ℂ)
    (hw₁ : Integrable w₁) (hw₂ : Integrable w₂) :
    (∑ i ∈ S, c i * primeCountCutoff P μ σ w₁ (n i) *
      primeCountCutoff Q ν τ w₂ (m i)) =
      ∫ t, ∫ s, ∑ i ∈ S,
        c i * (w₁ t * primeCutoffKernel P μ σ t (n i)) *
          (w₂ s * primeCutoffKernel Q ν τ s (m i)) := by
  exact finite_two_integrals S c
    (fun i t => w₁ t * primeCutoffKernel P μ σ t (n i))
    (fun i s => w₂ s * primeCutoffKernel Q ν τ s (m i))
    (fun i _ => integrable_weighted_primeCutoffKernel P μ σ (n i) hw₁)
    (fun i _ => integrable_weighted_primeCutoffKernel Q ν τ (m i) hw₂)

/-- The cutoff factors are exactly a Fourier average of multiplicative
finite-prime twists, with two unit-modulus constant phases. -/
theorem primeCountCutoff_twisted_pair_sum {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (n m : ι → ℕ) (f g : ℕ → ℂ) (P Q : Finset ℕ)
    (μ σ ν τ : ℝ) (w₁ w₂ : ℝ → ℂ)
    (hw₁ : Integrable w₁) (hw₂ : Integrable w₂) :
    (∑ i ∈ S, (c i * f (n i) * g (m i)) * primeCountCutoff P μ σ w₁ (n i) *
      primeCountCutoff Q ν τ w₂ (m i)) =
      ∫ t, ∫ s, w₁ t * w₂ s *
        (additiveCharacter (-t * μ / σ) 1 * additiveCharacter (-s * ν / τ) 1 *
          ∑ i ∈ S, c i * twistByPrimePhase f P (t / σ) (n i) *
            twistByPrimePhase g Q (s / τ) (m i)) := by
  rw [primeCountCutoff_pair_sum S (fun i => c i * f (n i) * g (m i))
    n m P Q μ σ ν τ w₁ w₂ hw₁ hw₂]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  dsimp only
  simp only [primeCutoffKernel, twistByPrimePhase, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem norm_primeCountCutoff_pair_sum_le {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (n m : ι → ℕ) (f g : ℕ → ℂ) (P Q : Finset ℕ)
    (μ σ ν τ : ℝ) (w₁ w₂ : ℝ → ℂ)
    (hw₁ : Integrable w₁) (hw₂ : Integrable w₂) (E : ℝ)
    (hbound : ∀ t s, ‖∑ i ∈ S, c i * twistByPrimePhase f P (t / σ) (n i) *
      twistByPrimePhase g Q (s / τ) (m i)‖ ≤ E) :
    ‖∑ i ∈ S, (c i * f (n i) * g (m i)) * primeCountCutoff P μ σ w₁ (n i) *
      primeCountCutoff Q ν τ w₂ (m i)‖ ≤
        E * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
  rw [primeCountCutoff_twisted_pair_sum S c n m f g P Q μ σ ν τ w₁ w₂ hw₁ hw₂]
  apply norm_two_weighted_integrals w₁ w₂ hw₁ hw₂
  intro t s
  simpa only [norm_mul, norm_additiveCharacter, one_mul] using hbound t s

end TwoPointCorrelations

end OAI
