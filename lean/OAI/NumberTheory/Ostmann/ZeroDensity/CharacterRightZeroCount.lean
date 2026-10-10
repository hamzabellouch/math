import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroCover

namespace OAI

/-! # Quantitative zero count in the right half of the critical strip -/

namespace Ostmann

open Metric Set
open scoped BigOperators Classical

/-- Sum of actual analytic multiplicities over any finite right-half family. -/
theorem PrimitiveComplexCharacter.right_zero_sum_bound (χ : PrimitiveComplexCharacter)
    (T : ℝ) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    ∑ z ∈ S, (characterZeroOrder χ z : ℝ) ≤
      (2 * T + 2) * (Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13)) := by
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hden : 0 < Real.log (14 / 13 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 ≤ Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13) := by
    apply div_nonneg _ hden.le
    apply Real.log_nonneg
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hT]
  have hfiber (n : ℤ) (hn : n ∈ characterOrdinateBins T) :
      ∑ z ∈ S.filter (fun z => ⌊z.im⌋ = n), (characterZeroOrder χ z : ℝ) ≤
        Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13) := by
    have hlocal := characterZeroOrder_sum_le_local χ ((n : ℝ) + 1 / 2)
      (S.filter fun z => ⌊z.im⌋ = n) (by
        intro z hz
        obtain ⟨hzS, hzn⟩ := Finset.mem_filter.mp hz
        simpa only [hzn] using character_floor_mem_disk z (hS z hzS).1 (hS z hzS).2.1)
    have hlocalR : ∑ z ∈ S.filter (fun z => ⌊z.im⌋ = n), (characterZeroOrder χ z : ℝ) ≤
        (characterLocalZeroMass χ ((n : ℝ) + 1 / 2) : ℝ) := by exact_mod_cast hlocal
    have hb := χ.local_zero_mass_bound ((n : ℝ) + 1 / 2)
    refine (hlocalR.trans hb).trans (div_le_div_of_nonneg_right ?_ hden.le)
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hn' := characterOrdinateBins_center_bound T n hn
    linarith
  calc
    _ = ∑ n ∈ characterOrdinateBins T,
        ∑ z ∈ S.filter (fun z => ⌊z.im⌋ = n), (characterZeroOrder χ z : ℝ) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun z hz => characterOrdinateBins_mem T z (hS z hz).2.2) _
    _ ≤ ∑ _n ∈ characterOrdinateBins T,
        Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13) :=
      Finset.sum_le_sum hfiber
    _ = ((characterOrdinateBins T).card : ℝ) *
        (Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (characterOrdinateBins_card T hT) hpos

end Ostmann

end OAI
