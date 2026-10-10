import OAI.NumberTheory.Ostmann.Construction.Poisson

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform Real
open FourierTransform MeasureTheory
namespace Ostmann.Construction

def schwartzScale (f : SchwartzMap ℝ ℂ) (a : ℝ) (ha : a ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha)) f

@[simp] theorem schwartzScale_apply (f : SchwartzMap ℝ ℂ) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    schwartzScale f a ha x = f (x*a) := rfl

theorem fourier_scale (f : ℝ → ℂ) (a ξ : ℝ) (ha : a ≠ 0) :
    𝓕 (fun x => f (x*a)) ξ = |a⁻¹| • 𝓕 f (ξ/a) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have heq (x : ℝ) : -(x*ξ) = -((x*a)*(ξ/a)) := by
    field_simp
  simp_rw [heq]
  exact Measure.integral_comp_mul_right (fun y => Real.fourierChar (-(y*(ξ/a))) • f y) a

theorem schwartzScale_fourier (f : SchwartzMap ℝ ℂ) (a ξ : ℝ) (ha : a ≠ 0) :
    𝓕 (schwartzScale f a ha) ξ = |a⁻¹| • 𝓕 f (ξ/a) := by
  exact fourier_scale f a ξ ha

end Ostmann.Construction

end

end OAI
