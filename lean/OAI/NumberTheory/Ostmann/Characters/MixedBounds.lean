import OAI.NumberTheory.Ostmann.Characters.MixedIndicator

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
variable {p : ℕ} [Fact p.Prime]

theorem norm_mixed_additiveTransform (S : Finset (ZMod p))
    (hS : S.Nonempty) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖FiniteField.mixedCorrelation (Supply.additiveTransform S) χ a‖ =
      Supply.density S / Real.sqrt (Supply.density S * (1-Supply.density S)) *
        translatedBias S χ⁻¹ a := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Fact.out (p:=p.Prime) |>.pos
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  rw [mixed_additiveTransform S χ hχ a]
  simp only [norm_mul, norm_inv, norm_div, norm_gaussSum χ hχ _
    (ZMod.isPrimitive_stdAddChar p), ZMod.card, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    norm_character_of_ne_zero χ⁻¹ (neg_ne_zero.mpr one_ne_zero)]
  simp only [translatedBias, translatedMean, norm_mul, norm_inv,
    Complex.norm_natCast, Supply.density, ZMod.card]
  field_simp

theorem balanced_sqrt_lower {σ : ℝ} (hlo : 1/4 ≤ σ) (hhi : σ ≤ 3/4) :
    1/4 ≤ Real.sqrt (σ*(1-σ)) := by
  have hprod : (1/4:ℝ)^2 ≤ σ*(1-σ) := by nlinarith [sq_nonneg (σ-1/2)]
  exact (Real.le_sqrt (by norm_num) (by nlinarith)).mpr hprod

theorem norm_mixed_additiveTransform_le (S : Finset (ZMod p))
    (hlo : 1/4 ≤ Supply.density S) (hhi : Supply.density S ≤ 3/4)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    ‖FiniteField.mixedCorrelation (Supply.additiveTransform S) χ a‖ ≤
      4 * translatedBias S χ⁻¹ a := by
  have hS : S.Nonempty := by
    by_contra he
    have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    norm_num [hs, Supply.density] at hlo
  rw [norm_mixed_additiveTransform S hS χ hχ a]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hl := balanced_sqrt_lower hlo hhi
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt
    (Supply.density S*(1-Supply.density S)))).mpr
  linarith
end Ostmann.Characters

end

end OAI
