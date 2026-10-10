import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroReflection

namespace OAI

/-! # Ordinary zero-count bound, with analytic multiplicities -/

namespace Ostmann

open Set
open scoped BigOperators Classical

theorem PrimitiveComplexCharacter.full_zero_sum_rate (χ : PrimitiveComplexCharacter)
    (T : ℝ) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T) :
    ∑ z ∈ S, (characterZeroOrder χ z : ℝ) ≤
      (32 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  let A := S.filter (fun z => 1 / 2 ≤ z.re)
  let B := S.filter (fun z => ¬ 1 / 2 ≤ z.re)
  let C := B.image (fun z : ℂ => 1 - z)
  have hA := χ.right_zero_sum_rate T hT A (by
    intro z hz
    obtain ⟨hzS, hzre⟩ := Finset.mem_filter.mp hz
    exact ⟨hzre, (hS z hzS).2.1.le, (hS z hzS).2.2⟩)
  have hC := χ.inverse.right_zero_sum_rate T hT C (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzS, hzre⟩ := Finset.mem_filter.mp hz
    obtain ⟨hr, hr', hi⟩ := hS z hzS
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg]
    exact ⟨by linarith, by linarith, hi⟩)
  have heq : ∑ z ∈ B, (characterZeroOrder χ z : ℝ) =
      ∑ w ∈ C, (characterZeroOrder χ.inverse w : ℝ) := by
    dsimp only [C]
    rw [Finset.sum_image (by
      intro z hz w hw he
      exact sub_right_injective he)]
    apply Finset.sum_congr rfl
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    obtain ⟨hr, hr', hi⟩ := hS z hzS
    have hh := characterZeroOrder_reflection χ (1 - z)
      (by simp; linarith) (by simp; linarith)
    rw [show (1 : ℂ) - (1 - z) = z by ring] at hh
    exact_mod_cast hh
  have hsplit : ∑ z ∈ S, (characterZeroOrder χ z : ℝ) =
      (∑ z ∈ A, (characterZeroOrder χ z : ℝ)) + ∑ z ∈ B, (characterZeroOrder χ z : ℝ) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun z => 1 / 2 ≤ z.re)
      (fun z => (characterZeroOrder χ z : ℝ))).symm
  rw [hsplit, heq]
  simp only [PrimitiveComplexCharacter.inverse_modulus] at hC
  calc
    _ ≤ (16 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) +
        (16 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) :=
      add_le_add hA hC
    _ = _ := by ring

end Ostmann

end OAI
