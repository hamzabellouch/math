import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! The normalized Euclidean heat kernel, with its integrable first derivatives. -/

noncomputable section
namespace ForcedComputation.PlaneHeat

open Real MeasureTheory Set Filter ShearFlows
open scoped Topology BigOperators ContDiff

def oneDim (t x : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(4 * t)⁻¹ * x ^ 2)

def oneDimDerivative (t x : ℝ) : ℝ := -(x / (2 * t)) * oneDim t x

theorem oneDim_nonneg (t x : ℝ) : 0 ≤ oneDim t x := by
  unfold oneDim
  positivity

theorem oneDim_integrable {t : ℝ} (ht : 0 < t) : Integrable (oneDim t) :=
  (integrable_exp_neg_mul_sq (by positivity : 0 < (4 * t)⁻¹)).const_mul _

theorem oneDim_integral {t : ℝ} (ht : 0 < t) : (∫ x, oneDim t x) = 1 := by
  unfold oneDim
  rw [integral_const_mul, integral_gaussian]
  have he : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by rw [div_inv_eq_mul]; ring
  rw [he, inv_mul_cancel₀]
  exact ne_of_gt (Real.sqrt_pos.2 (by positivity))

theorem oneDim_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (oneDim t) (oneDimDerivative t x) x := by
  have h := (((hasDerivAt_pow 2 x).const_mul (-(4 * t)⁻¹)).exp).const_mul
    (Real.sqrt (4 * Real.pi * t))⁻¹
  convert! h using 1
  simp only [oneDim, oneDimDerivative]
  field_simp [ht.ne']
  ring

theorem oneDim_smooth (t : ℝ) : ContDiff ℝ ∞ (oneDim t) := by
  unfold oneDim
  exact contDiff_const.mul
    ((contDiff_const.mul ((contDiff_id : ContDiff ℝ ∞ (fun x : ℝ => x)).pow 2)).exp)

private theorem firstMoment_Ioi {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2)) = (2 * b)⁻¹ := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    convert! (((hasDerivAt_pow 2 x).const_mul (-b)).exp).const_mul (-(2 * b)⁻¹)
      using 1
    field_simp [hb.ne']
    ring
  have hlim : Tendsto (fun x : ℝ => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  convert! integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn hlim using 1
  simp

theorem absoluteFirstMoment {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| * Real.exp (-b * x ^ 2)) = b⁻¹ := by
  calc
    _ = ∫ x : ℝ, (fun y => y * Real.exp (-b * y ^ 2)) |x| := by
      simp only [sq_abs]
    _ = 2 * ∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2) :=
      integral_comp_abs (f := fun y : ℝ => y * Real.exp (-b * y ^ 2))
    _ = b⁻¹ := by rw [firstMoment_Ioi hb]; field_simp

theorem oneDimDerivative_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (oneDimDerivative t) := by
  have h := (integrable_mul_exp_neg_mul_sq
    (by positivity : 0 < (4 * t)⁻¹)).const_mul
      (-(2 * t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹)
  convert! h using 1
  funext x
  simp only [oneDimDerivative, oneDim]
  ring

theorem oneDimDerivative_abs_integral {t : ℝ} (ht : 0 < t) :
    (∫ x, |oneDimDerivative t x|) = 2 / Real.sqrt (4 * Real.pi * t) := by
  have he (x : ℝ) : |oneDimDerivative t x| =
      ((2 * t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹) *
        (|x| * Real.exp (-(4 * t)⁻¹ * x ^ 2)) := by
    simp only [oneDimDerivative, oneDim, abs_mul, abs_neg, abs_div,
      abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, absoluteFirstMoment (by positivity)]
  field_simp
  ring

theorem oneDimDerivative_abs_integral_le {t : ℝ} (ht : 0 < t) :
    (∫ x, |oneDimDerivative t x|) ≤ 2 / Real.sqrt t := by
  rw [oneDimDerivative_abs_integral ht]
  apply div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr ht)
  apply Real.sqrt_le_sqrt
  have hp := Real.pi_gt_three
  nlinarith

def kernel (t : ℝ) (x : Plane) : ℝ := oneDim t (x 0) * oneDim t (x 1)

def kernelDerivative (t : ℝ) (j : Fin 2) (x : Plane) : ℝ :=
  -(x j / (2 * t)) * kernel t x

theorem kernel_smooth (t : ℝ) : ContDiff ℝ ∞ (kernel t) :=
  ((oneDim_smooth t).comp (contDiff_apply ℝ ℝ 0)).mul
    ((oneDim_smooth t).comp (contDiff_apply ℝ ℝ 1))

/-- The explicit first derivative in each Cartesian direction. -/
theorem kernel_fderiv_basis {t : ℝ} (ht : 0 < t) (x : Plane) (j : Fin 2) :
    fderiv ℝ (kernel t) x (Pi.single j 1) = kernelDerivative t j x := by
  let P₀ : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let P₁ : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have h₀ := (oneDim_hasDerivAt ht (x 0)).hasFDerivAt.comp x P₀.hasFDerivAt
  have h₁ := (oneDim_hasDerivAt ht (x 1)).hasFDerivAt.comp x P₁.hasFDerivAt
  have hd := h₀.mul h₁
  change HasFDerivAt (kernel t) _ x at hd
  rw [hd.fderiv]
  fin_cases j <;>
    simp [P₀, P₁, kernelDerivative, kernel, oneDimDerivative,
      ContinuousLinearMap.comp_apply] <;> ring

private theorem integrable_coordinate_product (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x : Plane => f (x 0) * g (x 1)) := by
  exact (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable (hf.mul_prod hg)

private theorem integral_coordinate_product (f g : ℝ → ℝ) :
    (∫ x : Plane, f (x 0) * g (x 1)) = (∫ x, f x) * ∫ x, g x := by
  calc
    _ = ∫ z : ℝ × ℝ, f z.1 * g z.2 :=
      (volume_preserving_finTwoArrow ℝ).integral_comp' _
    _ = _ := integral_prod_mul f g

theorem kernel_nonneg (t : ℝ) (x : Plane) : 0 ≤ kernel t x :=
  mul_nonneg (oneDim_nonneg t _) (oneDim_nonneg t _)

theorem kernel_integrable {t : ℝ} (ht : 0 < t) : Integrable (kernel t) :=
  integrable_coordinate_product _ _ (oneDim_integrable ht) (oneDim_integrable ht)

theorem kernel_integral {t : ℝ} (ht : 0 < t) : (∫ x : Plane, kernel t x) = 1 := by
  change (∫ x : Plane, oneDim t (x 0) * oneDim t (x 1)) = 1
  rw [integral_coordinate_product, oneDim_integral ht, one_mul]

theorem kernelDerivative_zero (t : ℝ) (x : Plane) :
    kernelDerivative t 0 x = oneDimDerivative t (x 0) * oneDim t (x 1) := by
  simp only [kernelDerivative, kernel, oneDimDerivative]
  ring

theorem kernelDerivative_one (t : ℝ) (x : Plane) :
    kernelDerivative t 1 x = oneDim t (x 0) * oneDimDerivative t (x 1) := by
  simp only [kernelDerivative, kernel, oneDimDerivative]
  ring

theorem kernelDerivative_integrable {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    Integrable (kernelDerivative t j) := by
  fin_cases j
  · change Integrable (kernelDerivative t 0)
    rw [show kernelDerivative t 0 = (fun x : Plane =>
      oneDimDerivative t (x 0) * oneDim t (x 1)) from funext (kernelDerivative_zero t)]
    exact integrable_coordinate_product _ _ (oneDimDerivative_integrable ht)
      (oneDim_integrable ht)
  · change Integrable (kernelDerivative t 1)
    rw [show kernelDerivative t 1 = (fun x : Plane =>
      oneDim t (x 0) * oneDimDerivative t (x 1)) from funext (kernelDerivative_one t)]
    exact integrable_coordinate_product _ _ (oneDim_integrable ht)
      (oneDimDerivative_integrable ht)

theorem kernelDerivative_abs_integral {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    (∫ x : Plane, |kernelDerivative t j x|) = 2 / Real.sqrt (4 * Real.pi * t) := by
  fin_cases j
  · change (∫ x : Plane, |kernelDerivative t 0 x|) = _
    rw [show kernelDerivative t 0 = (fun x : Plane =>
      oneDimDerivative t (x 0) * oneDim t (x 1)) from funext (kernelDerivative_zero t)]
    simp only [abs_mul,
      abs_of_nonneg (oneDim_nonneg t _)]
    rw [integral_coordinate_product (fun y => |oneDimDerivative t y|) (oneDim t), oneDim_integral ht,
      oneDimDerivative_abs_integral ht, mul_one]
  · change (∫ x : Plane, |kernelDerivative t 1 x|) = _
    rw [show kernelDerivative t 1 = (fun x : Plane =>
      oneDim t (x 0) * oneDimDerivative t (x 1)) from funext (kernelDerivative_one t)]
    simp only [abs_mul,
      abs_of_nonneg (oneDim_nonneg t _)]
    rw [integral_coordinate_product (oneDim t) (fun y => |oneDimDerivative t y|), oneDim_integral ht,
      oneDimDerivative_abs_integral ht, one_mul]

/-- The integrable gradient bound used in the short-time Volterra contraction. -/
theorem kernelDerivative_abs_integral_le {t : ℝ} (ht : 0 < t) (j : Fin 2) :
    (∫ x : Plane, |kernelDerivative t j x|) ≤ 2 / Real.sqrt t := by
  rw [kernelDerivative_abs_integral ht j, ← oneDimDerivative_abs_integral ht]
  exact oneDimDerivative_abs_integral_le ht

end ForcedComputation.PlaneHeat

end

end OAI
