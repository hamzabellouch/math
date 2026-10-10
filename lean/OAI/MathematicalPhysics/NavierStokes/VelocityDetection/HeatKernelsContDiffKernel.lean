import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernels

namespace OAI

noncomputable section
namespace VelocityDetection.HeatKernels
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open ProbabilityTheory SpatialCalculus

theorem contDiff_kernel (ν t : ℝ) : ContDiff ℝ ∞ (kernel ν t) := by
  unfold kernel
  fun_prop

theorem partialD_kernel (ν t : ℝ) (i : Fin 2) (X : Coord 2) :
    partialD i (kernel ν t) X = -(X i / (2 * ν * t)) * kernel ν t X := by
  let q : Coord 2 → ℝ := fun Y => -(Y 0 ^ 2 + Y 1 ^ 2) * (4 * ν * t)⁻¹
  have hq (Y : Coord 2) : HasFDerivAt q
      ((4 * ν * t)⁻¹ • -((2 * Y 0) • (ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ) +
        (2 * Y 1) • (ContinuousLinearMap.proj 1 : Coord 2 →L[ℝ] ℝ))) Y := by
    convert (((hasFDerivAt_apply (𝕜 := ℝ) 0 Y).pow 2).add
      ((hasFDerivAt_apply (𝕜 := ℝ) 1 Y).pow 2)).neg.const_mul (4 * ν * t)⁻¹ using 1 <;> try rfl
    · funext Z; dsimp [q]; ring
    · simp
  have hk (Y : Coord 2) : HasFDerivAt (kernel ν t)
      ((4 * Real.pi * ν * t)⁻¹ • (Real.exp (q Y) •
      ((4 * ν * t)⁻¹ • -((2 * Y 0) • (ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ) +
        (2 * Y 1) • (ContinuousLinearMap.proj 1 : Coord 2 →L[ℝ] ℝ))))) Y := by
    change HasFDerivAt (fun Z => (4 * Real.pi * ν * t)⁻¹ *
      Real.exp (-(Z 0 ^ 2 + Z 1 ^ 2) / (4 * ν * t))) _ Y
    simpa only [q, div_eq_mul_inv] using (hq Y).exp.const_mul (4 * Real.pi * ν * t)⁻¹
  rw [partialD_eq_fderiv i (fun Y => (hk Y).differentiableAt), (hk X).fderiv]
  simp only [smul_apply, neg_apply, add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  fin_cases i <;> simp [kernel, q, div_eq_mul_inv, mul_inv_rev] <;> ring

def momentKernel (i : Fin 2) (Y : Coord 2) : ℝ := Y i * normal 2 Y

theorem integrable_weighted_gaussian : Integrable (fun y : ℝ => y * gaussianPDFReal 0 1 y) := by
  have hh := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hh using 1
  funext y
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have he : -y ^ 2 / 2 = -(1 / 2 : ℝ) * y ^ 2 := by ring
  rw [he]
  ring

theorem integrable_momentKernel (i : Fin 2) : Integrable (momentKernel i) := by
  let w : Fin 2 → ℝ → ℝ := fun j y => if j = i then y * gaussianPDFReal 0 1 y else gaussianPDFReal 0 1 y
  have hw (j : Fin 2) : Integrable (w j) := by
    by_cases hj : j = i
    · simpa [w, hj] using integrable_weighted_gaussian
    · simpa [w, hj] using integrable_gaussianPDFReal 0 1
  have hh : Integrable (fun Y : Coord 2 => ∏ j : Fin 2, w j (Y j)) := Integrable.fintype_prod hw
  convert hh using 1
  funext Y
  fin_cases i <;> simp [momentKernel, normal, Fin.prod_univ_two, w] <;> ring

theorem partialD_kernel_rescale {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    partialD i (kernel ν t) = fun X =>
      -(Real.sqrt (2 * ν * t))⁻¹ *
        rescale (momentKernel i) (Real.sqrt (2 * ν * t)) X := by
  have hr : 0 < Real.sqrt (2 * ν * t) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (2 * ν * t) ^ 2 = 2 * ν * t := Real.sq_sqrt (by positivity)
  funext X
  rw [partialD_kernel, kernel_eq_rescale hν ht]
  simp only [rescale, momentKernel, Pi.smul_apply, smul_eq_mul]
  have hi : (2 * ν * t)⁻¹ = (Real.sqrt (2 * ν * t))⁻¹ * (Real.sqrt (2 * ν * t))⁻¹ := by
    calc
      (2 * ν * t)⁻¹ = (Real.sqrt (2 * ν * t) ^ 2)⁻¹ := congrArg Inv.inv hs.symm
      _ = _ := by rw [pow_two, mul_inv_rev]
  rw [div_eq_mul_inv, hi]
  ring

theorem integrable_partialD_kernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    Integrable (partialD i (kernel ν t)) := by
  rw [partialD_kernel_rescale hν ht]
  exact (integrable_rescale (integrable_momentKernel i)
    (Real.sqrt_pos.mpr (by positivity))).const_mul _

def absoluteMoment (i : Fin 2) : ℝ := ∫ Y, ‖momentKernel i Y‖

theorem absoluteMoment_nonneg (i : Fin 2) : 0 ≤ absoluteMoment i :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem integral_norm_partialD_kernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    (∫ Y, ‖partialD i (kernel ν t) Y‖) =
      (Real.sqrt (2 * ν * t))⁻¹ * absoluteMoment i := by
  rw [partialD_kernel_rescale hν ht]
  simp only [norm_mul, norm_neg, norm_inv,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  congr 1
  have hr : 0 < Real.sqrt (2 * ν * t) := Real.sqrt_pos.mpr (by positivity)
  have he : (fun Y => |rescale (momentKernel i) (Real.sqrt (2 * ν * t)) Y|) =
      rescale (fun Y => ‖momentKernel i Y‖) (Real.sqrt (2 * ν * t)) := by
    funext Y
    simp only [rescale, abs_mul, abs_inv, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.sqrt (2 * ν * t)))]
  rw [he, integral_rescale _ hr]
  rfl

theorem integral_norm_partialD_kernel_eq {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    (∫ Y, ‖partialD i (kernel ν t) Y‖) =
      (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt t)⁻¹ := by
  rw [integral_norm_partialD_kernel hν ht, Real.sqrt_mul (by positivity), mul_inv_rev]
  ring

end VelocityDetection.HeatKernels
end

end OAI
