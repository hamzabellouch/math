import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivativesFderiv

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
open ProbabilityTheory

def normal (n : ℕ) (X : Coord n) : ℝ := ∏ i : Fin n, gaussianPDFReal 0 1 (X i)

theorem normal_nonneg (n : ℕ) (X : Coord n) : 0 ≤ normal n X :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

theorem integrable_normal (n : ℕ) : Integrable (normal n) :=
  Integrable.fintype_prod (fun _ : Fin n => integrable_gaussianPDFReal 0 1)

@[simp] theorem integral_normal (n : ℕ) : ∫ X, normal n X = 1 := by
  simp only [normal]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one 0 one_ne_zero]

theorem normal_two (X : Coord 2) :
    normal 2 X = (2 * Real.pi)⁻¹ * Real.exp (-(X 0 ^ 2 + X 1 ^ 2) / 2) := by
  simp only [normal, Fin.prod_univ_two, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(X 0) ^ 2 / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(X 1) ^ 2 / 2)) =
        ((Real.sqrt (2 * Real.pi)) ^ 2)⁻¹ *
          Real.exp (-(X 0) ^ 2 / 2 + -(X 1) ^ 2 / 2) := by
      rw [← inv_pow, Real.exp_add]
      ring
    _ = _ := by
      rw [Real.sq_sqrt (by positivity)]
      congr 2
      ring

def rescale {n : ℕ} (k : Coord n → ℝ) (r : ℝ) (X : Coord n) : ℝ :=
  (r ^ n)⁻¹ * k (r⁻¹ • X)

theorem integrable_rescale {n : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    {r : ℝ} (hr : 0 < r) : Integrable (rescale k r) :=
  (hk.comp_smul (inv_ne_zero hr.ne')).const_mul _

theorem integral_rescale {n : ℕ} (k : Coord n → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ X, rescale k r X = ∫ X, k X := by
  simp only [rescale]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume k hr.le]
  simp only [Coord, Module.finrank_pi, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

theorem rescale_nonneg {n : ℕ} {k : Coord n → ℝ} (hk : ∀ X, 0 ≤ k X)
    {r : ℝ} (hr : 0 < r) (X : Coord n) : 0 ≤ rescale k r X :=
  mul_nonneg (by positivity) (hk _)

def kernel (ν t : ℝ) (X : Coord 2) : ℝ :=
  (4 * Real.pi * ν * t)⁻¹ * Real.exp (-(X 0 ^ 2 + X 1 ^ 2) / (4 * ν * t))

theorem kernel_eq_rescale {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    kernel ν t = rescale (normal 2) (Real.sqrt (2 * ν * t)) := by
  funext X
  have hs : Real.sqrt (2 * ν * t) ^ 2 = 2 * ν * t := Real.sq_sqrt (by positivity)
  simp only [kernel, rescale, normal_two, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, hs]
  rw [← mul_assoc]
  congr 1
  · field_simp [Real.pi_ne_zero, hν.ne', ht.ne']
    ring
  · congr 1
    field_simp [hν.ne', ht.ne']
    ring

theorem integrable_kernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    Integrable (kernel ν t) := by
  rw [kernel_eq_rescale hν ht]
  exact integrable_rescale (integrable_normal 2) (Real.sqrt_pos.mpr (by positivity))

@[simp] theorem integral_kernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    ∫ X, kernel ν t X = 1 := by
  rw [kernel_eq_rescale hν ht, integral_rescale _ (Real.sqrt_pos.mpr (by positivity)),
    integral_normal]

theorem kernel_nonneg {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (X : Coord 2) :
    0 ≤ kernel ν t X := by
  unfold kernel
  positivity

end VelocityDetection.HeatKernels
end

end OAI
