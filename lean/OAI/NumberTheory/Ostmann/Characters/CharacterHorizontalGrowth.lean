import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativeGrowth
import OAI.NumberTheory.Ostmann.Characters.CharacterSeparatedHeights

namespace OAI

/-! # Polynomial logarithmic-derivative bounds along both horizontal edges -/

namespace Ostmann

open Complex Metric Set

/-- One height controls both horizontal edges of the actual rectangular contour. -/
theorem exists_character_horizontal_bound (χ : PrimitiveComplexCharacter) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 3 ≤ T → ∃ t : ℝ,
      T < t ∧ t < T + 1 ∧ (∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t) ∧
      ∀ y : ℝ, y = t ∨ y = -t → ∀ σ ∈ Icc (-(1 / 2 : ℝ)) 2,
        ‖logDeriv χ.L ((σ : ℂ) + (y : ℂ) * I)‖ ≤ K * (T + 5) ^ 3 := by
  obtain ⟨K, hK, hgrowth⟩ := character_logDeriv_growth χ
  obtain ⟨D, hD, hheight⟩ := exists_character_separated_height χ
  refine ⟨K * (D + 1), by positivity, ?_⟩
  intro T hT
  obtain ⟨t, δ, ht, ht', hδ, hδbound, hzero, hsep⟩ := hheight T hT
  refine ⟨t, ht, ht', hzero, ?_⟩
  intro y hy σ hσ
  have htpos : 0 < t := by linarith
  have hyabs : |y| = t := by rcases hy with rfl | rfl <;> simp [abs_of_pos htpos]
  let s : ℂ := (σ : ℂ) + (y : ℂ) * I
  have hs : ‖s - characterZeroCenter y‖ ≤ 5 / 2 := by
    have he : s - characterZeroCenter y = ((σ - 2 : ℝ) : ℂ) := by
      dsimp [s, characterZeroCenter]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hsd : ∀ z ∈ characterContourZeros χ y, δ ≤ ‖s - z‖ := by
    intro z hz
    apply (hsep y hy z hz).trans
    have hh := abs_im_le_norm (s - z)
    simpa [s] using hh
  have hh := hgrowth y δ hδ s hs hsd
  rw [hyabs] at hh
  have hp : 1 + δ⁻¹ ≤ (D + 1) * (T + 5) ^ 2 := by
    have hsq : 1 ≤ (T + 5) ^ 2 := by nlinarith
    nlinarith
  calc
    _ ≤ K * (1 + t) * (1 + δ⁻¹) := hh
    _ ≤ K * (T + 5) * ((D + 1) * (T + 5) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hK.le
      · exact hp
      · positivity
      · positivity
    _ = _ := by ring

end Ostmann

end OAI
