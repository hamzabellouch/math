import OAI.Geometry.NodalSets.Elliptic.CorrugationHighRegime
import OAI.Geometry.NodalSets.Elliptic.CorrugationWellBound

namespace OAI

namespace Yau.Geometry
open Real
noncomputable section

theorem corrugation_actual_radial_loss : ∃ C : ℝ, 0 < C ∧
    ∀ (amp r χ L T : ℝ), 0 ≤ amp → amp ≤ 1 → 0 ≤ r →
      0 ≤ χ → χ ≤ 1 → 0 < L → 0 < T → ∀ k : ℕ,
      let l := corrugationSlope amp (1/4) r
      let d := max (-(deriv (corrugationSlope amp (1/4)) r)) 0
      (corrugationFrequency k*χ*l ≤ T →
        (corrugationScale L k)^2*corrugationFrequency k*χ*d ≤ C*corrugationLowRadialRate L T k) ∧
      (T < corrugationFrequency k*χ*l →
        (corrugationScale L k)^2*d ≤ C*corrugationHighRadialRate L T k*l) := by
  obtain ⟨C,hC,hbound⟩ := corrugationSlope_fractional_bound
  refine ⟨C,hC,?_⟩
  intro amp r χ L T hamp hamp1 hr hχ hχ1 hL hT k l d
  have hd : d ≤ C*l^((7:ℝ)/8) := hbound amp (1/4) r hamp hamp1 (by norm_num) (by norm_num) hr
  have hl : 0 ≤ l := corrugationSlope_nonneg hamp hr
  have hl1 : l ≤ 1 := corrugationSlope_le_one hamp hamp1 (by norm_num) (by norm_num) hr
  have hJ := corrugationFrequency_positive k
  constructor
  · intro hreg
    have h1 := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (mul_nonneg (sq_nonneg (corrugationScale L k)) hJ.le) hχ)
    have h2 := mul_le_mul_of_nonneg_left
      (corrugationLowErrorRate_bounds hL T k hχ hχ1 hl hl1 hreg).2 hC.le
    nlinarith
  · intro hreg
    have h1 := mul_le_mul_of_nonneg_left hd (sq_nonneg (corrugationScale L k))
    have h2 := mul_le_mul_of_nonneg_left
      (corrugationHighErrorRate_bounds hL hT k hχ hχ1 hl hl1 hreg).2 hC.le
    nlinarith

end
end Yau.Geometry

end OAI
