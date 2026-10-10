import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterHeightZeroCount
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourDiskZeros
import OAI.NumberTheory.Ostmann.Arithmetic.FiniteSeparatedHeight

namespace OAI

/-! # Paired contour heights with polynomially controlled separation from zeros -/

namespace Ostmann

open Complex Set
open scoped BigOperators Classical

theorem exists_character_separated_height (χ : PrimitiveComplexCharacter) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 3 ≤ T → ∃ t δ : ℝ,
      T < t ∧ t < T + 1 ∧ 0 < δ ∧ δ⁻¹ ≤ D * (T + 5) ^ 2 ∧
      (∀ z ∈ complexCharacterZeros χ, |z.im| ≠ t) ∧
      ∀ y : ℝ, y = t ∨ y = -t →
        ∀ z ∈ characterContourZeros χ y, δ ≤ |y - z.im| := by
  obtain ⟨C, hC, hcount⟩ := criticalZerosUpTo_card_polynomial χ
  refine ⟨4 * (C + 1), by positivity, ?_⟩
  intro T hT
  let S := (criticalZerosUpTo χ (T + 4)).image (fun z : ℂ => |z.im|)
  let δ := (4 * ((S.card : ℝ) + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsize : 2 * δ * (S.card : ℝ) < 1 := by
    dsimp [δ]
    have hr : (2 * (S.card : ℝ)) / (4 * ((S.card : ℝ) + 1)) < 1 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) S.card]
    convert hr using 1; ring
  obtain ⟨t, ht, hsep⟩ := exists_height_separated S T δ hδ hsize
  have htpos : 0 < t := by linarith [ht.1]
  have hcard : (S.card : ℝ) ≤ C * (T + 5) ^ 2 := by
    apply le_trans (show (S.card : ℝ) ≤ ((criticalZerosUpTo χ (T + 4)).card : ℝ) from
      by exact_mod_cast Finset.card_image_le)
    exact hcount T (by linarith)
  have hδbound : δ⁻¹ ≤ 4 * (C + 1) * (T + 5) ^ 2 := by
    dsimp [δ]
    rw [inv_inv]
    have hsq : 1 ≤ (T + 5) ^ 2 := by nlinarith
    nlinarith
  refine ⟨t, δ, ht.1, ht.2, hδ, hδbound, ?_, ?_⟩
  · intro z hz he
    have hzS : |z.im| ∈ S := Finset.mem_image.mpr
      ⟨z, mem_criticalZerosUpTo.mpr ⟨hz, by rw [he]; linarith [ht.2]⟩, rfl⟩
    have hh := hsep _ hzS
    rw [he, sub_self, abs_zero] at hh
    linarith
  · intro y hy z hz
    have hyabs : |y| = t := by rcases hy with rfl | rfl <;> simp [abs_of_pos htpos]
    obtain ⟨hzcrit, hzim⟩ := characterContourZeros_critical χ y (by rw [hyabs]; linarith [ht.1]) z hz
    have hzS : |z.im| ∈ S := Finset.mem_image.mpr
      ⟨z, mem_criticalZerosUpTo.mpr ⟨hzcrit, by rw [hyabs] at hzim; linarith [ht.2]⟩, rfl⟩
    have hh := hsep _ hzS
    have hab := abs_abs_sub_abs_le_abs_sub y z.im
    rw [hyabs] at hab
    exact hh.trans hab

end Ostmann

end OAI
