import OAI.NumberTheory.TwoPoint.Bounds.QualitativeRoughBins
import OAI.NumberTheory.TwoPoint.Bounds.RescaledPrefixSums

namespace OAI

/-! Finite assembly of the actual `u*w` expansion at `Y = floor(X/u)`.
The reciprocal weight of each retained divisor is preserved exactly, and
the long-average threshold is uniform over all admissible Fourier twists. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

structure RoughBinData where
  left : ℕ → ℂ
  right : ℕ → ℂ
  support : Finset ℕ
  coefficient : ℕ → ℂ

def RoughBinData.Admissible (d : RoughBinData) (f : ℕ → ℂ) (P : Finset ℕ)
    (M τ P₀ : ℝ) : Prop :=
  Multiplicative d.left ∧ OneBounded d.left ∧ OneBounded d.right ∧
  (∀ p, Nat.Prime p → p ∉ P → d.left p = f p) ∧
  (∀ z ∈ d.support, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧ HasNoPrimeFactorBelow P₀ z) ∧
  (∀ z ∈ d.support, ‖d.coefficient z‖ ≤ 1)

/-- Uniform rough-shift cancellation summed over the finite retained-
divisor family, with total weight `sum |a_u|/u`. Functions and coefficients
may be chosen after the common long-average threshold. -/
theorem qualitative_divisor_transfer (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (U : Finset ℕ) (a : ℕ → ℂ) (H τ : ℝ) (P : ℕ → Finset ℕ)
        (l : ℕ) [NeZero l] (residue : ℕ → ZMod l),
      1 < τ → τ < 2 → (∀ u ∈ U, 0 < u) →
      (∀ u ∈ U, Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ H / (u : ℝ)) →
      (∀ u ∈ U, H / (u : ℝ) ≤ Real.exp (C₀ * B)) →
      ∀ᶠ X : ℕ in atTop, ∀ d : ℕ → RoughBinData,
      (∀ u ∈ U, (d u).Admissible f (P u) (H / (u : ℝ)) τ
        (Real.exp (B ^ (9999 / 10000 : ℝ)))) →
      ‖(∑ u ∈ U, a u * positivePrefix
        (weightedRoughShiftProfile (progressionSequence (d u).left l (residue u))
          (d u).right (d u).support (d u).coefficient h) (X / u)) / (X : ℂ)‖ ≤
        C * B ^ (-10001 / 10000 : ℝ) * (∑ u ∈ U, ‖a u‖ / (u : ℝ)) := by
  obtain ⟨C, hC, hrough⟩ := qualitative_rough_shifts_real_bins hM hMRT hfnp hf h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrough, eventually_ge_atTop 1] with B hb hB
  intro U a H τ P l _ residue hτ₁ hτ₂ hU hMlower hMupper
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let F : ℕ → RoughBinData → ℕ → ℂ := fun u d =>
    weightedRoughShiftProfile (progressionSequence d.left l (residue u))
      d.right d.support d.coefficient h
  let Valid : ℕ → RoughBinData → Prop := fun u d =>
    d.Admissible f (P u) (H / (u : ℝ)) τ (Real.exp (B ^ (9999 / 10000 : ℝ)))
  have hF : ∀ u ∈ U, ∀ᶠ Y : ℕ in atTop,
      ∀ d : RoughBinData, Valid u d → ‖positivePrefix (F u d) Y / (Y : ℂ)‖ ≤
        C * B ^ (-10001 / 10000 : ℝ) := by
    intro u hu
    filter_upwards [hb (P u) (H / (u : ℝ)) τ hτ₁ hτ₂ (hMlower u hu) (hMupper u hu)]
      with Y hy
    intro d hd
    exact hy d.left d.right hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1
      l (residue u) d.support d.coefficient hd.2.2.2.2.1 hd.2.2.2.2.2
  exact finite_rescaled_prefix_bound U a F Valid
    (C * B ^ (-10001 / 10000 : ℝ)) (by positivity) hU hF

end TwoPointCorrelations

end OAI
