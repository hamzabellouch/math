import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspMassIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspSectionHardy
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The sharp radial inequality is integrated over the actual horizontal
period cell. Both sides are justified by the proved scalar integrability. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

theorem cubicThetaCusp_integrated_hardy (δ : SL(2,Eisenstein)) (F : cubicThetaSmoothTests) :
    (∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)≤
    ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ),
      ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2 := by
  have hm := cubicThetaCuspCutoff_mass_integrable δ F
  have hd := cubicThetaCuspCutoff_derivative_integrable δ F
  have hm' : Integrable (fun y : ℂ × ℝ => ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3)
      ((volume.restrict cubicThetaHorizontalCell).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hm
  have hd' : Integrable (fun y : ℂ × ℝ => ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2)
      ((volume.restrict cubicThetaHorizontalCell).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hd
  change (∫ y, ‖cubicThetaCuspCutoffSection δ F y.1 y.2‖^2/y.2^3
    ∂((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)))≤
    (∫ y, ‖deriv (cubicThetaCuspCutoffSection δ F y.1) y.2‖^2/y.2
      ∂((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
        (cubicThetaHorizontalCell ×ˢ Ioi (0:ℝ)))
  rw [← Measure.prod_restrict,integral_prod _ hm',integral_prod _ hd']
  exact integral_mono hm'.integral_prod_left hd'.integral_prod_left
    (fun z => cubicThetaCuspSection_hardy δ F z)

end CubicFirstMoment

end

end OAI
