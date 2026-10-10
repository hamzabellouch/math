import OAI.MeasureTheory.Falconer.Angular.CircleTests
import OAI.MeasureTheory.Falconer.Radial.RadialShellMeasure

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceAngularTransform (ρ : Measure Plane) (X : Set Plane) (M : ℝ)
    (b : Plane → UnitCircle → ℂ) (r : ℝ) (ω : UnitCircle) : ℂ :=
  M⁻¹ • ∫ x in X, Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω ∂ρ

noncomputable def sourceAngularMoment (U : ℝ × UnitCircle → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ‖U (r, ω)‖ₑ^2 ∂sourceArcLength

noncomputable def sourceAngularH (a v : ℝ) (Ψ : ℝ → ℝ) (U V : ℝ × UnitCircle → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(2*(v-a))) * ∫⁻ r,
    sourceAngularMoment U r * sourceAngularMoment V r ∂sourceAngularShellMeasure v Ψ

theorem measurable_sourceAngularMoment (U : ℝ × UnitCircle → ℂ) (hU : Measurable U) :
    Measurable (sourceAngularMoment U) := (hU.enorm.pow_const 2).lintegral_prod_right'

theorem sourceAngularH_two_profile (a v : ℝ) (Ψ : ℝ → ℝ)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V) :
    sourceAngularH a v Ψ U V ≤
      (sourceAngularH a v Ψ U U)^(1/2 : ℝ) * (sourceAngularH a v Ψ V V)^(1/2 : ℝ) := by
  let C := ENNReal.ofReal ((2:ℝ)^(2*(v-a)))
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hCt : C ≠ ∞ := ENNReal.ofReal_ne_top
  have hCs : C^(1/2 : ℝ)*C^(1/2 : ℝ) = C := by
    rw [← ENNReal.rpow_add _ _ hC0 hCt]
    norm_num
  have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (sourceAngularShellMeasure v Ψ) hpq
    (measurable_sourceAngularMoment U hU).aemeasurable
    (measurable_sourceAngularMoment V hV).aemeasurable
  simp only [ENNReal.rpow_two, pow_two] at hh
  unfold sourceAngularH
  change C * _ ≤ (C * _)^(1/2 : ℝ) * (C * _)^(1/2 : ℝ)
  apply (mul_le_mul_right hh C).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  calc
    _ = (C^(1/2 : ℝ)*C^(1/2 : ℝ)) * _ := by rw [hCs]
    _ = _ := by ac_rfl

end PlanarFalconer

end OAI
