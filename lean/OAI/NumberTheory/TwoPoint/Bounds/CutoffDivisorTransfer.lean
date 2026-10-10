import OAI.NumberTheory.TwoPoint.Bounds.RoughCutoffAverage

namespace OAI

/-! Finite retained-divisor assembly for the actual two-cutoff averages.
The original nonpretentious factor may be either member of the pair. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem qualitative_cutoff_rough_shifts_either (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ P Q : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ Q, Nat.Prime p) →
      ∀ (M τ : ℝ), 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M → M ≤ Real.exp (C₀ * B) →
      ∀ᶠ Y : ℕ in atTop, ∀ (l : ℕ) [NeZero l] (a : ZMod l) (μ σ ν ρ : ℝ)
        (w₁ w₂ : ℝ → ℂ), Integrable w₁ → Integrable w₂ →
      ∀ (Z : Finset ℕ) (c : ℕ → ℂ),
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      (∀ z ∈ Z, ‖c z‖ ≤ 1) →
      ‖cutoffRoughAverage f g l a P Q μ σ ν ρ w₁ w₂ Z c h Y‖ ≤
        (C * B ^ (-10001 / 10000 : ℝ)) * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
  rcases hnp with hnp | hnp
  · obtain ⟨C, hC, hb⟩ := qualitative_cutoff_rough_shifts hM hMRT hnp hf hfm h hh C₀ hC₀
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with B hb
    intro P Q hP _ M τ hτ₁ hτ₂ hMlower hMupper
    filter_upwards [hb P hP M τ hτ₁ hτ₂ hMlower hMupper] with Y hy
    intro l _ a μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c hZ hc
    exact hy g hg l a Q μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c hZ hc
  · obtain ⟨C, hC, hb⟩ := qualitative_cutoff_rough_shifts_right hM hMRT hnp hg hgm h hh C₀ hC₀
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with B hb
    intro P Q _ hQ M τ hτ₁ hτ₂ hMlower hMupper
    filter_upwards [hb Q hQ M τ hτ₁ hτ₂ hMlower hMupper] with Y hy
    intro l _ a μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c hZ hc
    exact hy f hf l a P μ σ ν ρ w₁ w₂ hw₁ hw₂ Z c hZ hc

structure RoughCoefficients where
  support : Finset ℕ
  coefficient : ℕ → ℂ

def RoughCoefficients.InBin (d : RoughCoefficients) (M τ P₀ : ℝ) : Prop :=
  (∀ z ∈ d.support, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧ HasNoPrimeFactorBelow P₀ z) ∧
  (∀ z ∈ d.support, ‖d.coefficient z‖ ≤ 1)

noncomputable def cutoffRoughProfile (f g : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (P Q : Finset ℕ) (μ σ ν ρ : ℝ) (w₁ w₂ : ℝ → ℂ)
    (d : RoughCoefficients) (h : ℕ) : ℕ → ℂ :=
  weightedRoughShiftProfile
    (progressionSequence (fun n => f n * primeCountCutoff P μ σ w₁ n) l a)
    (fun n => g n * primeCountCutoff Q ν ρ w₂ n) d.support d.coefficient h

/-- The actual cutoff terms at scales `floor(X/u)` retain exactly the
reciprocal divisor mass. The finite coefficient family remains uniform. -/
theorem qualitative_cutoff_divisor_transfer (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (U : Finset ℕ) (a : ℕ → ℂ) (H τ : ℝ) (P Q : ℕ → Finset ℕ),
      (∀ u ∈ U, ∀ p ∈ P u, Nat.Prime p) →
      (∀ u ∈ U, ∀ p ∈ Q u, Nat.Prime p) →
      1 < τ → τ < 2 → (∀ u ∈ U, 0 < u) →
      (∀ u ∈ U, Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ H / (u : ℝ)) →
      (∀ u ∈ U, H / (u : ℝ) ≤ Real.exp (C₀ * B)) →
      ∀ (l : ℕ) [NeZero l] (residue : ℕ → ZMod l) (μ σ ν ρ : ℕ → ℝ)
        (w₁ w₂ : ℝ → ℂ), Integrable w₁ → Integrable w₂ →
      ∀ᶠ X : ℕ in atTop, ∀ d : ℕ → RoughCoefficients,
      (∀ u ∈ U, (d u).InBin (H / (u : ℝ)) τ
        (Real.exp (B ^ (9999 / 10000 : ℝ)))) →
      ‖(∑ u ∈ U, a u * positivePrefix
        (cutoffRoughProfile f g l (residue u) (P u) (Q u) (μ u) (σ u) (ν u) (ρ u)
          w₁ w₂ (d u) h) (X / u)) / (X : ℂ)‖ ≤
        ((C * B ^ (-10001 / 10000 : ℝ)) * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖)) *
          (∑ u ∈ U, ‖a u‖ / (u : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := qualitative_cutoff_rough_shifts_either hM hMRT hf hg hfm hgm hnp h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop 0] with B hb hB
  intro U a H τ P Q hP hQ hτ₁ hτ₂ hU hMlower hMupper l _ residue μ σ ν ρ w₁ w₂ hw₁ hw₂
  let F : ℕ → RoughCoefficients → ℕ → ℂ := fun u d =>
    cutoffRoughProfile f g l (residue u) (P u) (Q u) (μ u) (σ u) (ν u) (ρ u) w₁ w₂ d h
  let Valid : ℕ → RoughCoefficients → Prop := fun u d =>
    d.InBin (H / (u : ℝ)) τ (Real.exp (B ^ (9999 / 10000 : ℝ)))
  have hF : ∀ u ∈ U, ∀ᶠ Y : ℕ in atTop, ∀ d : RoughCoefficients,
      Valid u d → ‖positivePrefix (F u d) Y / (Y : ℂ)‖ ≤
        (C * B ^ (-10001 / 10000 : ℝ)) * (∫ t, ‖w₁ t‖) * (∫ s, ‖w₂ s‖) := by
    intro u hu
    filter_upwards [hb (P u) (Q u) (hP u hu) (hQ u hu) (H / (u : ℝ)) τ
      hτ₁ hτ₂ (hMlower u hu) (hMupper u hu)] with Y hy
    intro d hd
    exact hy l (residue u) (μ u) (σ u) (ν u) (ρ u) w₁ w₂ hw₁ hw₂
      d.support d.coefficient hd.1 hd.2
  exact finite_rescaled_prefix_bound U a F Valid _
    (mul_nonneg (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hB _))
      (integral_nonneg (fun _ => norm_nonneg _))) (integral_nonneg (fun _ => norm_nonneg _))) hU hF

end TwoPointCorrelations

end OAI
