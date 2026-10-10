import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothRectangleResidues
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothOriginResidue

namespace OAI

/-! # The exact truncated smooth explicit formula

The contour encloses all actual critical zeros of bounded height and the
origin. Its zero sum is a finite sum with analytic multiplicities.
-/

namespace Ostmann

open Complex Set
open scoped BigOperators Classical Interval

noncomputable def criticalZerosUpTo (χ : PrimitiveComplexCharacter) (T : ℝ) : Finset ℂ :=
  (χ.strip_zeros_finite T).toFinset

@[simp] theorem mem_criticalZerosUpTo {χ : PrimitiveComplexCharacter} {T : ℝ} {z : ℂ} :
    z ∈ criticalZerosUpTo χ T ↔ z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T := by
  exact Set.Finite.mem_toFinset _

theorem smoothContour_truncated (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (T : ℝ) (hT : 0 < T)
    (hheight : ∀ z ∈ complexCharacterZeros χ, |z.im| ≠ T) :
    rectangleBoundaryIntegral
      (fun z => (-deriv χ.L z / χ.L z) * smoothContourWeight X z)
      (-(1 / 2)) 2 (-T) T =
      -(2 * (Real.pi : ℂ) * I) *
        ((∑ z ∈ criticalZerosUpTo χ T,
          (analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z) + smoothTrivialZeroTerm χ) := by
  let S := insert (0 : ℂ) (criticalZerosUpTo χ T)
  have hinside : ∀ z ∈ S, -(1 / 2 : ℝ) < z.re ∧ z.re < 2 ∧ -T < z.im ∧ z.im < T := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · change -(1 / 2 : ℝ) < 0 ∧ (0 : ℝ) < 2 ∧ -T < 0 ∧ 0 < T
      exact ⟨by norm_num, by norm_num, by linarith, hT⟩
    · obtain ⟨hz, hi⟩ := mem_criticalZerosUpTo.mp hz
      have hi' := lt_of_le_of_ne hi (hheight z hz)
      have hab := abs_lt.mp hi'
      exact ⟨by linarith [hz.1], by linarith [hz.2.1], hab.1, hab.2⟩
  have hzeros : ∀ z ∈ uIcc (-(1 / 2 : ℝ)) 2 ×ℂ uIcc (-T) T, χ.L z = 0 → z ∈ S := by
    intro z hz hzero
    have hr : -(1 / 2 : ℝ) ≤ z.re := (show z.re ∈ Icc (-(1 / 2 : ℝ)) 2 by
      simpa only [uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 2), mem_preimage] using hz.1).1
    rcases χ.contour_zero_location z hr hzero with rfl | hcrit
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply mem_criticalZerosUpTo.mpr
      refine ⟨hcrit, abs_le.mpr ?_⟩
      simpa only [uIcc_of_le (by linarith : -T ≤ T), mem_preimage, mem_Icc] using hz.2
  have hzero : (0 : ℂ) ∉ criticalZerosUpTo χ T := by
    simp [complexCharacterZeros]
  have hmain := smoothContour_rectangle_residues χ X hX (-(1 / 2)) 2 (-T) T S hinside hzeros
  have horigin : (analyticOrderNatAt χ.L 0 : ℂ) * smoothContourWeight X 0 = smoothTrivialZeroTerm χ := by
    have hh := smoothContour_origin_residue_value χ X
    linear_combination -hh
  simpa only [S, Finset.sum_insert hzero, horigin, add_comm] using hmain

end Ostmann

end OAI
