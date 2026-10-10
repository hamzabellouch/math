import OAI.Analysis.KadisonKastler.FourierModulation
import OAI.Analysis.KadisonKastler.RealNestMultiplier

namespace OAI

/-! # Characters permute the concrete frequency nest -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sign and the `2*pi` normalization in the frequency shift. -/
theorem regularFrequencyProjection_character_intertwine (a s : ℝ) :
    regularFrequencyProjection (H := H) a *
        (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularFrequencyProjection (a - 2 * Real.pi * s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularFrequencyProjection a
    ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) : RegularCoreHilbert H) =
    𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyProjection (a - 2 * Real.pi * s) f))
  rw [fourier_regularCharacterUnitary]
  apply Lp.ext
  have hp := regularFrequencyProjection_apply_fourier a
    ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
  rw [fourier_regularCharacterUnitary] at hp
  filter_upwards [hp,
    regularTranslateApply_ae (-s) (𝓕 f : RegularCoreHilbert H),
    regularTranslateApply_ae (-s)
      (𝓕 (regularFrequencyProjection (a - 2 * Real.pi * s) f) : RegularCoreHilbert H),
    (measurePreserving_add_right volume (-s)).quasiMeasurePreserving.ae_eq_comp
      (regularFrequencyProjection_apply_fourier (a - 2 * Real.pi * s) f)]
    with t h₁ h₂ h₃ h₄
  simp only [Function.comp_def] at h₄
  rw [h₁, h₃, h₄]
  have hcut : a / (2 * Real.pi) < t ↔
      (a - 2 * Real.pi * s) / (2 * Real.pi) < t + -s := by
    have hpos : 0 < 2 * Real.pi := by positivity
    rw [div_lt_iff₀ hpos, div_lt_iff₀ hpos]
    constructor <;> intro h <;> nlinarith
  by_cases ht : a / (2 * Real.pi) < t
  · simpa only [Set.indicator_apply, Set.mem_Ioi, ht, hcut.mp ht, ite_true] using h₂
  · have ht' := mt hcut.mpr ht
    simp only [Set.indicator_apply, Set.mem_Ioi, ht, ht', ite_false]

/-- Conjugation by a character sends one upper-frequency cut to another. -/
theorem regularFrequencyProjection_character_conj (a s : ℝ) :
    unitaryConj (regularCharacterUnitary (H := H) (2 * Real.pi * s))
      (regularFrequencyProjection (a - 2 * Real.pi * s)) =
        regularFrequencyProjection a := by
  unfold unitaryConj
  rw [← regularFrequencyProjection_character_intertwine, mul_assoc,
    Unitary.mul_star_self_of_mem (regularCharacterUnitary (H := H) (2 * Real.pi * s)).property,
    mul_one]

/-- The constructed increasing nest meets the character-permutation
hypothesis of invariant nest averaging, for every real character. -/
theorem regularFrequencyNest_character_perm (a b : ℝ) :
    ∃ c, regularFrequencyNest (H := H) a =
      unitaryConj (regularCharacterUnitary b) (regularFrequencyNest c) := by
  refine ⟨a + b, ?_⟩
  have h := regularFrequencyProjection_character_conj (H := H) (-a) (b / (2 * Real.pi))
  have hb : 2 * Real.pi * (b / (2 * Real.pi)) = b := by
    field_simp [Real.pi_ne_zero]
  rw [hb] at h
  simpa only [regularFrequencyNest, neg_add_rev, sub_eq_add_neg, add_comm (-b) (-a)]
    using h.symm

/-- Actual Fourier cuts can now be used directly in the multiplier
construction; no abstract projection-chain or permutation input remains. -/
theorem exists_frequency_nest_multiplier [TopologicalSpace.SeparableSpace H]
    (hNest : PublishedRealNestDistance.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ t, ‖F t‖ ≤ C)
    {δ : ℝ} (hδ : 0 < δ)
    (hdefect : ∀ a, ‖(1 - regularFrequencyNest a) *
      regularFieldOperator volume F hF C hC * regularFrequencyNest a‖ ≤ δ) :
    ∃ (B : ℝ → H →L[ℂ] H) (S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H),
      PreservesProjectionNest regularFrequencyNest S ∧
      (∀ x, AEStronglyMeasurable (fun t => B t x) volume) ∧
      RepresentsOperatorField volume B S ∧
      (∀ᵐ t, ‖B t‖ ≤ C + 2 * δ) ∧ (∀ᵐ t, ‖B t - F t‖ ≤ 2 * δ) :=
  exists_real_nest_multiplier hNest hSpectral hDiagonal regularFrequencyNest
    regularFrequencyNest_isStarProjection regularFrequencyNest_mono
    regularFrequencyNest_character_perm F hF hC0 hC hδ hdefect

end

end KadisonKastler

end OAI
