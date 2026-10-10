import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm
import OAI.Analysis.CircleDomains.Sobolev.CircleEnergy

namespace OAI

/-! The full spherical energy of a circle coordinate is controlled by
its two real partial derivatives, with no choice of global real lift. -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circle_gradient_energy_eq_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → UnitAddCircle}
    (hf : MemLp (circleGradient f) 2 μ) :
    (∫ x, fieldEnergy (circleGradient f) (fun z => sphericalMetricFactor z • 1) x ∂μ) =
      (eLpNorm (fun x => circleFDeriv f x (1, 0)) 2 μ).toReal ^ 2 +
        (eLpNorm (fun x => circleFDeriv f x (0, 1)) 2 μ).toReal ^ 2 := by
  calc
    _ = ∫ x, (circleGradient f x).1 ^ 2 + (circleGradient f x).2 ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fieldEnergy_spherical (circleGradient f))
    _ = (∫ x, (circleGradient f x).1 ^ 2 ∂μ) +
        (∫ x, (circleGradient f x).2 ^ 2 ∂μ) :=
      integral_add hf.fst.integrable_sq hf.snd.integrable_sq
    _ = _ := by
      rw [integral_sq_eq_eLpNorm_toReal_sq hf.fst, integral_sq_eq_eLpNorm_toReal_sq hf.snd]
      rfl

 theorem circle_gradient_norm_le_partial_norms
    {μ : Measure (ℝ × ℝ)} {f : (ℝ × ℝ) → UnitAddCircle}
    (hf : MemLp (circleGradient f) 2 μ) :
    Real.sqrt (∫ x, fieldEnergy (circleGradient f)
      (fun z => sphericalMetricFactor z • 1) x ∂μ) ≤
      (eLpNorm (fun x => circleFDeriv f x (1, 0)) 2 μ).toReal +
        (eLpNorm (fun x => circleFDeriv f x (0, 1)) 2 μ).toReal := by
  rw [circle_gradient_energy_eq_norms hf, Real.sqrt_le_iff]
  constructor
  · positivity
  · have hx := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => circleFDeriv f x (1, 0)) 2 μ)
    have hy := ENNReal.toReal_nonneg
      (a := eLpNorm (fun x => circleFDeriv f x (0, 1)) 2 μ)
    nlinarith [mul_nonneg hx hy]

end CircleDomainRigidity

end

end OAI
