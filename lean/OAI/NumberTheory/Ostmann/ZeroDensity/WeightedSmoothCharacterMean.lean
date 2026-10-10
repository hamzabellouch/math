import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrincipalMean
import OAI.NumberTheory.Ostmann.Characters.SparseConductorCutoff

namespace OAI

/-! # Weighted smooth character means at the actual truncation cutoff -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- A finite coefficient bound costs no factor equal to the number of characters. -/
theorem weighted_smooth_character_error (F : Finset PrimitiveComplexCharacter)
    (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ) (B X : ℝ)
    (hc₀ : ‖c₀‖ ≤ B) (hc : ∀ χ ∈ F, ‖c χ‖ ≤ B) :
    ‖c₀ * smoothMangoldtMean 1 1 X +
        ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character X -
        c₀ * smoothPrincipalMain X‖ ≤
      B * (smoothPrincipalError X +
        ∑ χ ∈ F, ‖smoothMangoldtMean χ.modulus χ.character X‖) := by
  have he : c₀ * smoothMangoldtMean 1 1 X +
      ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character X -
      c₀ * smoothPrincipalMain X =
      c₀ * (smoothMangoldtMean 1 1 X - smoothPrincipalMain X) +
      ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character X := by ring
  rw [he]
  calc
    _ ≤ ‖c₀ * (smoothMangoldtMean 1 1 X - smoothPrincipalMain X)‖ +
        ∑ χ ∈ F, ‖c χ * smoothMangoldtMean χ.modulus χ.character X‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ B * smoothPrincipalError X +
        ∑ χ ∈ F, B * ‖smoothMangoldtMean χ.modulus χ.character X‖ := by
      simp only [norm_mul, smoothPrincipalError]
      gcongr
      exact hc _ (by assumption)
    _ = _ := by rw [← Finset.mul_sum, mul_add]

theorem weighted_sparse_character_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C A D : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (F : Finset PrimitiveComplexCharacter) (c : PrimitiveComplexCharacter → ℂ) (c₀ : ℂ),
        (∀ χ ∈ F, χ.modulus ≤ sparseConductorCutoff C L) →
        (∀ χ ∈ F, some χ ≠ exception) → ‖c₀‖ ≤ Real.exp (A * L) →
        (∀ χ ∈ F, ‖c χ‖ ≤ Real.exp (A * L)) →
        ‖c₀ * smoothMangoldtMean 1 1 (Real.exp (Real.exp L)) +
          ∑ χ ∈ F, c χ * smoothMangoldtMean χ.modulus χ.character (Real.exp (Real.exp L)) -
          c₀ * smoothPrincipalMain (Real.exp (Real.exp L))‖ ≤
          Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [smooth_primitive_family_decay Z hD hR P hPNT (2 * C + 3) (D + A)
    (by linarith), eventual_sparseConductorCutoff C hC] with L hmean hcut
  obtain ⟨exception, hmean⟩ := hmean (sparseConductorCutoff C L) hcut.1 hcut.2.1 hcut.2.2
  refine ⟨exception, ?_⟩
  intro F c c₀ hF hFE hc₀ hc
  have hh := weighted_smooth_character_error F c c₀ (Real.exp (A * L))
    (Real.exp (Real.exp L)) hc₀ hc
  calc
    _ ≤ _ := hh
    _ ≤ Real.exp (A * L) * (Real.exp (Real.exp L) * Real.exp (-(D + A) * L)) :=
      mul_le_mul_of_nonneg_left (hmean F hF hFE) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_left_comm (Real.exp (A * L)), ← Real.exp_add]
      congr 2
      ring

end Ostmann

end OAI
