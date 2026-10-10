import OAI.Analysis.LipschitzHilbert.Phase.PlanarSliceFourierAngular
import OAI.Analysis.LipschitzHilbert.Fourier.PlanarCovariantJet

namespace OAI

/-! Vertical differentiation of a general planar Schwartz function has
the Fourier multiplier `2π i η`. Consequently every scaled covariant
vertical jet used in the packet construction preserves spectral zeros.
The proof uses one-dimensional differentiation and product Fubini, so
it does not impose a tensor decomposition on the planar packet. -/

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

private def verticalSchwartzSlice (f : SchwartzMap (ℝ × ℝ) ℂ) (x : ℝ) :
    SchwartzMap ℝ ℂ :=
  planarSchwartzSlice (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) f) x 0

private theorem verticalSchwartzSlice_apply (f : SchwartzMap (ℝ × ℝ) ℂ)
    (x y : ℝ) : verticalSchwartzSlice f x y = f (x, y) := by
  change f (x + 0 * y, y) = f (x, y)
  simp

private theorem verticalSchwartzSlice_deriv (f : SchwartzMap (ℝ × ℝ) ℂ)
    (x : ℝ) : deriv (verticalSchwartzSlice f x) =
      (verticalSchwartzSlice (planarVerticalDerivative f) x : ℝ → ℂ) := by
  funext y
  have hline : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h := (f.hasFDerivAt (x, y)).comp_hasDerivAt y hline
  change HasDerivAt (fun t => f (x, t)) (fderiv ℝ f (x, y) (0, 1)) y at h
  have hslice : (verticalSchwartzSlice f x : ℝ → ℂ) = fun t => f (x, t) :=
    funext (verticalSchwartzSlice_apply f x)
  rw [hslice, h.deriv, verticalSchwartzSlice_apply, planarVerticalDerivative_apply]

private theorem verticalSchwartzSlice_fourier_deriv
    (f : SchwartzMap (ℝ × ℝ) ℂ) (x η : ℝ) :
    𝓕 (verticalSchwartzSlice (planarVerticalDerivative f) x) η =
      (2 * Real.pi * Complex.I * η) * 𝓕 (verticalSchwartzSlice f x) η := by
  have hi : Integrable (deriv (verticalSchwartzSlice f x)) := by
    rw [verticalSchwartzSlice_deriv]
    exact (verticalSchwartzSlice (planarVerticalDerivative f) x).integrable
  have h := congrFun (Real.fourier_deriv (verticalSchwartzSlice f x).integrable
    (verticalSchwartzSlice f x).differentiable hi) η
  rw [verticalSchwartzSlice_deriv] at h
  simpa only [SchwartzMap.fourier_coe, smul_eq_mul] using h

theorem planarFourier_integrand_integrable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency : ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      Real.fourierChar (-(z.1 * frequency.1 + z.2 * frequency.2)) • f z)
      (volume.prod volume) := by
  apply f.integrable.norm.mono'
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      f.continuous).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Circle.norm_smul]
    exact le_rfl

private theorem planarFourier_eq_vertical_integral
    (f : SchwartzMap (ℝ × ℝ) ℂ) (ξ η : ℝ) :
    planarFourier f (ξ, η) = ∫ x,
      Real.fourierChar (-(x * ξ)) • 𝓕 (verticalSchwartzSlice f x) η := by
  unfold planarFourier
  rw [integral_prod _ (planarFourier_integrand_integrable f (ξ, η))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [Real.inner_apply, verticalSchwartzSlice_apply]
  change (∫ y, Real.fourierChar (-(x * ξ + y * η)) • f (x, y)) =
    (Real.fourierChar (-(x * ξ)) : ℂ) •
      (∫ y, Real.fourierChar (-(y * η)) • f (x, y))
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  change Real.fourierChar (-(x * ξ + y * η)) • f (x, y) =
    Real.fourierChar (-(x * ξ)) • (Real.fourierChar (-(y * η)) • f (x, y))
  rw [← mul_smul, ← Real.fourierChar.map_add_eq_mul]
  congr 2
  ring

/-- The exact vertical-derivative multiplier for the product-Lebesgue
Fourier transform, with mathlib's `2π` convention. -/
theorem planarFourier_verticalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ)
    (ξ η : ℝ) :
    planarFourier (planarVerticalDerivative f) (ξ, η) =
      (2 * Real.pi * Complex.I * η) * planarFourier f (ξ, η) := by
  rw [planarFourier_eq_vertical_integral, planarFourier_eq_vertical_integral]
  simp_rw [verticalSchwartzSlice_fourier_deriv]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

theorem planarFourier_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (frequency : ℝ × ℝ) :
    planarFourier (c • f : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      c * planarFourier f frequency := by
  unfold planarFourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [smul_apply, Circle.smul_def, smul_eq_mul]
  ring

theorem planarFourier_sub (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency : ℝ × ℝ) :
    planarFourier (f - g : SchwartzMap (ℝ × ℝ) ℂ) frequency =
      planarFourier f frequency - planarFourier g frequency := by
  unfold planarFourier
  simp only [sub_apply, smul_sub]
  exact integral_sub (planarFourier_integrand_integrable f frequency)
    (planarFourier_integrand_integrable g frequency)

theorem planarFourier_covariantDerivative (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency ξ η : ℝ) :
    planarFourier (planarCovariantDerivative f frequency) (ξ, η) =
      (2 * Real.pi * Complex.I * η - (frequency : ℂ) * Complex.I) *
        planarFourier f (ξ, η) := by
  rw [planarCovariantDerivative, planarFourier_sub, planarFourier_smul,
    planarFourier_verticalDerivative]
  ring

/-- All three scaled covariant jets retain every spectral zero of the
original general planar Schwartz packet. -/
theorem planarFourier_covariantJet_eq_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale : ℝ) (i : Fin 3) (ξ η : ℝ)
    (hzero : planarFourier f (ξ, η) = 0) :
    planarFourier (planarCovariantJet f frequency scale i) (ξ, η) = 0 := by
  fin_cases i
  · exact hzero
  · change planarFourier ((scale : ℂ) • planarCovariantDerivative f frequency :
      SchwartzMap (ℝ × ℝ) ℂ) (ξ, η) = 0
    rw [planarFourier_smul, planarFourier_covariantDerivative, hzero, mul_zero, mul_zero]
  · change planarFourier ((scale : ℂ) • planarCovariantDerivative
      ((scale : ℂ) • planarCovariantDerivative f frequency) frequency :
      SchwartzMap (ℝ × ℝ) ℂ) (ξ, η) = 0
    rw [planarFourier_smul, planarFourier_covariantDerivative, planarFourier_smul,
      planarFourier_covariantDerivative, hzero, mul_zero, mul_zero, mul_zero, mul_zero]

theorem planarAngularFourier_verticalDerivative (f : SchwartzMap (ℝ × ℝ) ℂ)
    (ξ η : ℝ) :
    planarAngularFourier (planarVerticalDerivative f) (ξ, η) =
      (Complex.I * η) * planarAngularFourier f (ξ, η) := by
  unfold planarAngularFourier
  rw [planarFourier_verticalDerivative]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem planarAngularFourier_covariantDerivative (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency ξ η : ℝ) :
    planarAngularFourier (planarCovariantDerivative f frequency) (ξ, η) =
      (Complex.I * (η - frequency)) * planarAngularFourier f (ξ, η) := by
  unfold planarAngularFourier
  rw [planarFourier_covariantDerivative]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem planarAngularFourier_covariantJet_eq_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (frequency scale : ℝ) (i : Fin 3) (ξ η : ℝ)
    (hzero : planarAngularFourier f (ξ, η) = 0) :
    planarAngularFourier (planarCovariantJet f frequency scale i) (ξ, η) = 0 :=
  planarFourier_covariantJet_eq_zero f frequency scale i _ _ hzero

end LipschitzHilbert

end

end OAI
