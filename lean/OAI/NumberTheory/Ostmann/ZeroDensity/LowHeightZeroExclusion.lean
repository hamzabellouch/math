import OAI.NumberTheory.Ostmann.ZeroDensity.LowHeightShiftedBound
import OAI.NumberTheory.Ostmann.ZeroDensity.ZeroFreeNumerics
import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterConjugateZeros

namespace OAI

/-! # The local exceptional-zero argument with explicit margins -/

namespace Ostmann

open Complex
open scoped ComplexConjugate

theorem near_axis_zero_indices_unique (χ : PrimitiveRealCharacter) (δ R : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10)
    (hupper : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (i j : ℕ)
    (hi : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re)
    (hj : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re)
    (hiy : |((realCharacterActualZeros χ).zeros i).im| ≤ δ / 2)
    (hjy : |((realCharacterActualZeros χ).zeros j).im| ≤ δ / 2) : i = j := by
  by_contra hij
  have hpair := (shifted_real_zero_pair_le χ ((1 + δ : ℝ) : ℂ)
    (by simp; linarith) (by simp; linarith) i j hij).trans hupper
  rw [realZeroKernel_complex, realZeroKernel_complex] at hpair
  have hmi := real_zero_near_mass δ (1 + δ - ((realCharacterActualZeros χ).zeros i).re)
    _ hδ (by linarith [((realCharacterActualZeros χ).in_strip i).2]) (by linarith) hiy
  have hmj := real_zero_near_mass δ (1 + δ - ((realCharacterActualZeros χ).zeros j).re)
    _ hδ (by linarith [((realCharacterActualZeros χ).in_strip j).2]) (by linarith) hjy
  have hp := mul_le_mul_of_nonneg_left hpair hδ.le
  have he : δ * (1 / δ + R) = 1 + δ * R := by field_simp
  rw [he, mul_add] at hp
  linarith

theorem near_zero_small_height (χ : PrimitiveRealCharacter) (δ S : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : δ * (2 * Real.log χ.modulus + S) ≤ 1 / 10)
    (hupper : ∀ t : ℝ, |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + 2 * Real.log χ.modulus + S)
    (i : ℕ) (hi : 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re)
    (hiy : |((realCharacterActualZeros χ).zeros i).im| ≤ 1) :
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
  have he : δ * (3 / δ + realZeroKernel δ (2 * ρ.im) + 2 * Real.log χ.modulus + S) =
      3 + δ * realZeroKernel δ (2 * ρ.im) + δ * (2 * Real.log χ.modulus + S) := by
    field_simp; ring
  rw [he] at hp
  have hm := real_zero_shifted_mass δ a hδ ha ha'
  have hk := real_zero_double_height_mass δ ρ.im hδ (le_of_not_gt hy)
  simp only [div_eq_mul_inv] at hm
  linarith

/-- The local inequalities force every exceptional low-height zero to be real,
and count multiplicities: two distinct indices are impossible. -/
theorem near_low_height_zeros_real_unique (χ : PrimitiveRealCharacter) (δ R S : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : δ * R ≤ 1 / 10)
    (hS : δ * (2 * Real.log χ.modulus + S) ≤ 1 / 10)
    (hreal : shiftedRealCharacterZeroSum χ ((1 + δ : ℝ) : ℂ) ≤ 1 / δ + R)
    (hshift : ∀ t : ℝ, |t| ≤ 1 →
      4 * shiftedRealCharacterZeroSum χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * I) ≤
        3 / δ + realZeroKernel δ (2 * t) + 2 * Real.log χ.modulus + S) :
    (∀ i, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ 1 →
      ((realCharacterActualZeros χ).zeros i).im = 0) ∧
    (∀ i j, 1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros i).re →
      1 - δ / 20 ≤ ((realCharacterActualZeros χ).zeros j).re →
      |((realCharacterActualZeros χ).zeros i).im| ≤ 1 →
      |((realCharacterActualZeros χ).zeros j).im| ≤ 1 → i = j) := by
  have hsmall := near_zero_small_height χ δ S hδ hδ1 hS hshift
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
