import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatKernel

namespace OAI

/-! The normalized Euclidean Gaussian satisfies the heat equation. -/

noncomputable section
namespace ForcedComputation.PlaneHeat
open ShearFlows
open scoped ContDiff BigOperators

def oneDimSecond (t x : ℝ) : ℝ := (x^2 / (4*t^2) - 1/(2*t)) * oneDim t x

theorem oneDimDerivative_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (oneDimDerivative t) (oneDimSecond t x) x := by
  have h := (((hasDerivAt_id x).div_const (2*t)).neg).mul (oneDim_hasDerivAt ht x)
  convert! h using 1
  dsimp [oneDimDerivative, oneDimSecond]
  ring

theorem oneDim_time_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => oneDim s x) (oneDimSecond t x) t := by
  have hA : 0 < 4 * Real.pi * t := by positivity
  have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    convert! (hasDerivAt_id t).const_mul (4 * Real.pi) using 1
    simp only [mul_one]
  have hs := hlin.sqrt hA.ne'
  have hp : HasDerivAt (fun s : ℝ => (Real.sqrt (4 * Real.pi * s))⁻¹)
      (-(1 / (2*t)) * (Real.sqrt (4 * Real.pi * t))⁻¹) t := by
    convert! hs.inv (Real.sqrt_pos.mpr hA).ne' using 1
    field_simp [ht.ne', (Real.sqrt_pos.mpr hA).ne']
    nlinarith [Real.sq_sqrt hA.le,
      Real.sq_sqrt (show 0 ≤ t * 4 * Real.pi by positivity)]
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(4*s)⁻¹*x^2))
      (x^2 / (4*t^2) * Real.exp (-(4*t)⁻¹*x^2)) t := by
    have h := (((((hasDerivAt_id t).const_mul 4).inv
      (mul_ne_zero (by norm_num) ht.ne')).neg).mul_const (x^2)).exp
    simp only [id_eq, Pi.inv_apply, Pi.neg_apply] at h
    convert! h using 1
    field_simp [ht.ne']
  convert! hp.mul he using 1
  dsimp [oneDimSecond, oneDim]
  ring

def kernelSecond (t : ℝ) (j : Fin 2) (x : Plane) : ℝ :=
  (x j ^ 2 / (4*t^2) - 1/(2*t)) * kernel t x

theorem kernel_time_hasDerivAt {t : ℝ} (ht : 0 < t) (x : Plane) :
    HasDerivAt (fun s => kernel s x) (∑ j : Fin 2, kernelSecond t j x) t := by
  have h := (oneDim_time_hasDerivAt ht (x 0)).mul (oneDim_time_hasDerivAt ht (x 1))
  convert! h using 1
  dsimp [kernelSecond, oneDimSecond, kernel]
  rw [Fin.sum_univ_two]
  ring

theorem kernelDerivative_fderiv_basis {t : ℝ} (ht : 0 < t) (x : Plane) (j : Fin 2) :
    fderiv ℝ (kernelDerivative t j) x (Pi.single j 1) = kernelSecond t j x := by
  have hp := ((ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).hasFDerivAt.const_mul
    (-(2*t)⁻¹)).mul ((kernel_smooth t).differentiable (by simp) x).hasFDerivAt
  have he : (fun y : Plane => -(2*t)⁻¹ * y j * kernel t y) = kernelDerivative t j := by
    funext y
    unfold kernelDerivative
    ring
  change HasFDerivAt (fun y : Plane => -(2*t)⁻¹ * y j * kernel t y) _ x at hp
  rw [he] at hp
  change HasFDerivAt (kernelDerivative t j) _ x at hp
  rw [hp.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, kernel_fderiv_basis ht, smul_eq_mul]
  dsimp [kernelSecond, kernelDerivative]
  ring

end ForcedComputation.PlaneHeat

end

end OAI
