import OAI.NumberTheory.Ostmann.ZeroDensity.FullHeightRealShiftedBound
import OAI.NumberTheory.Ostmann.ZeroDensity.LowHeightZeroExclusion

namespace OAI

/-! # The exceptional real-zero argument in a bounded ordinate range -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

theorem near_real_zero_small_ordinate (χ : PrimitiveRealCharacter) (δ S T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : δ * S ≤ 1 / 10)
    (hupper : ∀ t : ℝ, |t| ≤ T →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + S)
    (i : ℕ) (hi : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re)
    (hiy : |((realCharacterActualZeros χ).zeros i).im| ≤ T) :
    |((realCharacterActualZeros χ).zeros i).im| < δ / 2 := by
  by_contra hy
  let ρ := (realCharacterActualZeros χ).zeros i
  let a : ℝ := 1 + δ - ρ.re
  let s : ℂ := ((1 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I
  have ha : δ ≤ a := by dsimp [a, ρ]; linarith [((realCharacterActualZeros χ).in_strip i).2]
  have ha' : a ≤ (21 / 20) * δ := by dsimp [a, ρ]; linarith
  have hterm := shifted_real_zero_term_le χ s (by dsimp [s]; simp; linarith)
    (by dsimp [s]; simp; linarith) i
  have hdiff : s - (realCharacterActualZeros χ).zeros i = (a : ℂ) := by
    apply Complex.ext <;> simp [s, a, ρ]
  rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re] at hterm
  have hb := (mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 4)).trans (hupper ρ.im hiy)
  have hp := mul_le_mul_of_nonneg_left hb hδ.le
  have he : δ * (3 / δ + realZeroKernel δ (2 * ρ.im) + S) =
      3 + δ * realZeroKernel δ (2 * ρ.im) + δ * S := by field_simp
  rw [he] at hp
  have hm := real_zero_shifted_mass δ a hδ ha ha'
  have hk := real_zero_double_height_mass δ ρ.im hδ (le_of_not_gt hy)
  simp only [div_eq_mul_inv] at hm
  linarith

theorem near_real_zeros_real_unique_height (χ : PrimitiveRealCharacter) (δ R S T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10) (hS : δ * S ≤ 1 / 10)
    (hreal : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (hshift : ∀ t : ℝ, |t| ≤ T →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + S) :
    (∀ i, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ T →
      ((realCharacterActualZeros χ).zeros i).im = 0) ∧
    (∀ i j, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ T →
      |((realCharacterActualZeros χ).zeros j).im| ≤ T → i = j) := by
  have hsmall := near_real_zero_small_ordinate χ δ S T hδ hδ1 hS hshift
  have huniq := near_axis_zero_indices_unique χ δ R hδ hδ1 hR hreal
  constructor
  · intro i hi hiy
    obtain ⟨j, hj⟩ := realCharacterActualZeros_conjugate χ i
    have hjre : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re := by simpa [hj] using hi
    have hjim : |((realCharacterActualZeros χ).zeros j).im| ≤ δ / 2 := by
      simpa [hj] using (hsmall i hi hiy).le
    have hij := huniq i j hi hjre (hsmall i hi hiy).le hjim
    rw [← hij] at hj
    have hh := congrArg Complex.im hj
    simp only [Complex.conj_im] at hh
    linarith
  · intro i j hi hj hiy hjy
    exact huniq i j hi hj (hsmall i hi hiy).le (hsmall j hj hjy).le

end Ostmann

end OAI
