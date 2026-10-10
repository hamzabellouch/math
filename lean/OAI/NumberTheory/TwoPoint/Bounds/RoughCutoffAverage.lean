import OAI.NumberTheory.TwoPoint.Bounds.QualitativeDivisorTransferRight
import OAI.NumberTheory.TwoPoint.Bounds.FourierPrimeCutoff

namespace OAI

/-! The actual two-cutoff rough correlation is a finite Fourier average of
the already bounded rough correlations. Both original-factor choices are
supported, with every cutoff parameter uniform after the long threshold. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical FourierTransform

noncomputable def roughPairCoefficient (c : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (Y : ℕ) (i : ℕ × ℕ) : ℂ :=
  if ((i.1 + 1 : ℕ) : ZMod l) = a then (c i.2 / (i.2 : ℂ)) / (Y : ℂ) else 0

lemma weightedRoughShiftAverage_eq_pairSum (f g : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (Z : Finset ℕ) (c : ℕ → ℂ) (h Y : ℕ) :
    weightedRoughShiftAverage (progressionSequence f l a) g Z c h Y =
      ∑ i ∈ (range Y).product Z,
        roughPairCoefficient c l a Y i * f (i.1 + 1) * g (i.1 + 1 + h * i.2) := by
  unfold weightedRoughShiftAverage positivePrefix weightedRoughShiftProfile
  rw [sum_div]
  calc
    _ = ∑ n ∈ range Y, ∑ z ∈ Z,
        roughPairCoefficient c l a Y (n, z) * f (n + 1) * g (n + 1 + h * z) := by
      apply sum_congr rfl
      intro n _
      rw [sum_div]
      apply sum_congr rfl
      intro z _
      unfold roughPairCoefficient progressionSequence
      by_cases hn : ((n + 1 : ℕ) : ZMod l) = a
      · simp only [hn, ite_true]
        ring
      · simp only [hn, ite_false, zero_mul, mul_zero, zero_div]
    _ = _ := (Finset.sum_product (range Y) Z
      (fun i => roughPairCoefficient c l a Y i * f (i.1 + 1) * g (i.1 + 1 + h * i.2))).symm

noncomputable def cutoffRoughAverage (f g : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (P Q : Finset ℕ) (μ σ ν τ : ℝ) (w₁ w₂ : ℝ → ℂ)
    (Z : Finset ℕ) (c : ℕ → ℂ) (h Y : ℕ) : ℂ :=
  weightedRoughShiftAverage
    (progressionSequence (fun n => f n * primeCountCutoff P μ σ w₁ n) l a)
    (fun n => g n * primeCountCutoff Q ν τ w₂ n) Z c h Y

lemma cutoffRoughAverage_fourier (f g : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (P Q : Finset ℕ) (μ σ ν τ : ℝ) (φ₁ φ₂ : ℝ → ℂ)
    (hc₁ : Continuous φ₁) (hc₂ : Continuous φ₂)
    (hi₁ : Integrable φ₁) (hi₂ : Integrable φ₂)
    (hF₁ : Integrable (𝓕 φ₁)) (hF₂ : Integrable (𝓕 φ₂))
    (Z : Finset ℕ) (c : ℕ → ℂ) (h Y : ℕ) :
    cutoffRoughAverage f g l a P Q μ σ ν τ (𝓕 φ₁) (𝓕 φ₂) Z c h Y =
      weightedRoughShiftAverage
        (progressionSequence (fun n => f n * φ₁ (((finitePrimeDivisorCount P n : ℝ) - μ) / σ)) l a)
        (fun n => g n * φ₂ (((finitePrimeDivisorCount Q n : ℝ) - ν) / τ)) Z c h Y := by
  simp only [cutoffRoughAverage, primeCountCutoff_fourier P μ σ φ₁ hc₁ hi₁ hF₁,
    primeCountCutoff_fourier Q ν τ φ₂ hc₂ hi₂ hF₂]

theorem norm_cutoffRoughAverage_le (f g : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (P Q : Finset ℕ) (μ σ ν τ : ℝ) (w₁ w₂ : ℝ → ℂ)
    (hw₁ : Integrable w₁) (hw₂ : Integrable w₂)
    (Z : Finset ℕ) (c : ℕ → ℂ) (h Y : ℕ) (E : ℝ)
    (hbound : ∀ t s, ‖weightedRoughShiftAverage
      (progressionSequence (twistByPrimePhase f P (t / σ)) l a)
      (twistByPrimePhase g Q (s / τ)) Z c h Y‖ ≤ E) :
    ‖cutoffRoughAverage f g l a P Q μ σ ν τ w₁ w₂ Z c h Y‖ ≤
      E * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
  have heq : cutoffRoughAverage f g l a P Q μ σ ν τ w₁ w₂ Z c h Y =
      ∑ i ∈ (range Y).product Z,
        (roughPairCoefficient c l a Y i * f (i.1 + 1) * g (i.1 + 1 + h * i.2)) *
          primeCountCutoff P μ σ w₁ (i.1 + 1) *
          primeCountCutoff Q ν τ w₂ (i.1 + 1 + h * i.2) := by
    rw [cutoffRoughAverage, weightedRoughShiftAverage_eq_pairSum]
    apply sum_congr rfl
    intro i _
    ring
  rw [heq]
  apply norm_primeCountCutoff_pair_sum_le ((range Y).product Z)
    (roughPairCoefficient c l a Y) (fun i => i.1 + 1) (fun i => i.1 + 1 + h * i.2)
    f g P Q μ σ ν τ w₁ w₂ hw₁ hw₂ E
  intro t s
  simpa only [weightedRoughShiftAverage_eq_pairSum] using hbound t s

theorem qualitative_cutoff_rough_shifts (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) (hfm : Multiplicative f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      ∀ (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M → M ≤ Real.exp (C₀ * B) →
      ∀ᶠ Y : ℕ in atTop, ∀ g : ℕ → ℂ, OneBounded g →
      ∀ (l : ℕ) [NeZero l] (a : ZMod l) (Q : Finset ℕ) (μ σ ν ρ : ℝ)
        (w₁ w₂ : ℝ → ℂ), Integrable w₁ → Integrable w₂ →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖cutoffRoughAverage f g l a P Q μ σ ν ρ w₁ w₂ Z c h Y‖ ≤
        (C * B ^ (-10001 / 10000 : ℝ)) * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_rough_shifts_real_bins hM hMRT hfnp hf h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough] with B hb
  intro P hP M τ hτ₁ hτ₂ hMlower hMupper
  filter_upwards [hb P M τ hτ₁ hτ₂ hMlower hMupper] with Y hy
  intro g hg l _ a Q μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c hZ hc
  apply norm_cutoffRoughAverage_le f g l a P Q μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c h Y
  intro t s
  exact hy (twistByPrimePhase f P (t / σ)) (twistByPrimePhase g Q (s / ρ))
    (hfm.twistByPrimePhase P hP _) (hf.twistByPrimePhase P _)
    (hg.twistByPrimePhase Q _) (fun p hp hout => twistByPrimePhase_prime_outside f P hP _ hp hout)
    l a Z c hZ hc

theorem qualitative_cutoff_rough_shifts_right (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {g : ℕ → ℂ}
    (hgnp : UniformlyNonpretentious g) (hg : OneBounded g) (hgm : Multiplicative g)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, Nat.Prime p) →
      ∀ (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M → M ≤ Real.exp (C₀ * B) →
      ∀ᶠ Y : ℕ in atTop, ∀ f : ℕ → ℂ, OneBounded f →
      ∀ (l : ℕ) [NeZero l] (a : ZMod l) (P : Finset ℕ) (μ σ ν ρ : ℝ)
        (w₁ w₂ : ℝ → ℂ), Integrable w₁ → Integrable w₂ →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖cutoffRoughAverage f g l a P Q μ σ ν ρ w₁ w₂ Z c h Y‖ ≤
        (C * B ^ (-10001 / 10000 : ℝ)) * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_rough_shifts_real_bins_right hM hMRT hgnp hg h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough] with B hb
  intro Q hQ M τ hτ₁ hτ₂ hMlower hMupper
  filter_upwards [hb Q M τ hτ₁ hτ₂ hMlower hMupper] with Y hy
  intro f hf l _ a P μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c hZ hc
  apply norm_cutoffRoughAverage_le f g l a P Q μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c h Y
  intro t s
  exact hy (twistByPrimePhase f P (t / σ)) (twistByPrimePhase g Q (s / ρ))
    (hf.twistByPrimePhase P _) (hgm.twistByPrimePhase Q hQ _)
    (hg.twistByPrimePhase Q _) (fun p hp hout => twistByPrimePhase_prime_outside g Q hQ _ hp hout)
    l a Z c hZ hc

end TwoPointCorrelations

end OAI
