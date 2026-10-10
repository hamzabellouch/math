import OAI.Geometry.CylinderCovering.Angular.GeneralAssembly
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.AngularGeneral

theorem relativeCost_le_totalArea {τ : ℝ} {D : Data}
    (hunit : ∀ j < D.count,
      ‖lowerAxis τ D j‖ = 1 ∧ ‖upperAxis τ D j‖ = 1) :
    relativeCost τ D ≤ totalArea τ D / TriangularCovering.H := by
  unfold relativeCost totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [add_div]
  exact add_le_add
    (div_le_div_of_nonneg_left ENNReal.toReal_nonneg TriangularCovering.H_pos
      (TriangularCovering.shadowArea_ge_H (hunit j j.isLt).1))
    (div_le_div_of_nonneg_left ENNReal.toReal_nonneg TriangularCovering.H_pos
      (TriangularCovering.shadowArea_ge_H (hunit j j.isLt).2))

theorem strict_costs_of_ratio {τ : ℝ} {D : Data}
    (hunit : ∀ j < D.count,
      ‖lowerAxis τ D j‖ = 1 ∧ ‖upperAxis τ D j‖ = 1)
    (hratio : totalArea τ D / TriangularCovering.H < 1/2) :
    totalArea τ D < TriangularCovering.A_min/2 ∧ relativeCost τ D < 1/2 := by
  constructor
  · rw [TriangularCovering.projection_minimum]
    have hh := (div_lt_iff₀ TriangularCovering.H_pos).mp hratio
    linarith only [hh]
  · exact (relativeCost_le_totalArea hunit).trans_lt hratio

theorem cost_conclusions {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) (hτ : 0 < τ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/8) (hE : 0 ≤ E)
    (hτ1 : τ^2 ≤ 1) (hsmall : E*τ^2 ≤ 1/16)
    (hsave : 2*(3*E+1)*τ^2 < 1/240-2*η)
    (hunit : ∀ j < D.count,
      ‖lowerAxis τ D j‖ = 1 ∧ ‖upperAxis τ D j‖ = 1)
    (harea : totalArea τ D / TriangularCovering.H = integralCost τ D) :
    |totalArea τ D / TriangularCovering.H-(1/2+(2*η-1/240)*τ^2)| ≤
      2*(3*E+1)*τ^4 ∧
      totalArea τ D < TriangularCovering.A_min/2 ∧ relativeCost τ D < 1/2 := by
  have herror := integralCost_expansion hD hη hη1 hE hτ1 hsmall
  rw [← harea] at herror
  have hratio := GeneralCapArea.strict_half_of_area_error hτ herror hsave
  exact ⟨herror,strict_costs_of_ratio hunit hratio⟩

end CylinderCovering.AngularGeneral

end

end OAI
