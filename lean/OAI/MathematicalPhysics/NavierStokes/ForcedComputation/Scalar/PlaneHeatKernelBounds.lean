import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatKernel

namespace OAI

/-! An integrable Gaussian majorant for all spatial shifts in a bounded set. -/

noncomputable section
namespace ForcedComputation.PlaneHeat

open Real MeasureTheory Set ShearFlows
open scoped Topology BigOperators

/-- A slower Gaussian, used to dominate bounded translations of the heat kernel. -/
def envelopeCore (t y : ℝ) : ℝ := Real.exp (-((4 * t)⁻¹ / 2) * y ^ 2)

def envelopeMoment (t R y : ℝ) : ℝ := (|y| + R) * envelopeCore t y

def shiftCoefficient (t R : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp ((4 * t)⁻¹ * R ^ 2)

theorem envelopeCore_pos (t y : ℝ) : 0 < envelopeCore t y := Real.exp_pos _

theorem shiftCoefficient_nonneg (t R : ℝ) : 0 ≤ shiftCoefficient t R := by
  unfold shiftCoefficient
  positivity

private theorem shifted_square (R z y : ℝ) (_hR : 0 ≤ R) (hz : |z| ≤ R) :
    y ^ 2 / 2 - R ^ 2 ≤ (z - y) ^ 2 := by
  have hz' := abs_le.mp hz
  have hzz : z ^ 2 ≤ R ^ 2 := by nlinarith
  nlinarith [sq_nonneg (y - 2 * z)]

theorem oneDim_shift_le {t : ℝ} (ht : 0 < t) {R z : ℝ}
    (hR : 0 ≤ R) (hz : |z| ≤ R) (y : ℝ) :
    oneDim t (z - y) ≤ shiftCoefficient t R * envelopeCore t y := by
  have ha : 0 ≤ (4 * t)⁻¹ := by positivity
  have hs := mul_le_mul_of_nonneg_left (shifted_square R z y hR hz) ha
  have he : -(4 * t)⁻¹ * (z - y) ^ 2 ≤
      (4 * t)⁻¹ * R ^ 2 + (-((4 * t)⁻¹ / 2) * y ^ 2) := by linarith
  unfold oneDim shiftCoefficient envelopeCore
  calc
    _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ *
        Real.exp ((4 * t)⁻¹ * R ^ 2 + (-((4 * t)⁻¹ / 2) * y ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

theorem oneDimDerivative_shift_le {t : ℝ} (ht : 0 < t) {R z : ℝ}
    (hR : 0 ≤ R) (hz : |z| ≤ R) (y : ℝ) :
    |oneDimDerivative t (z - y)| ≤
      (shiftCoefficient t R / (2 * t)) * envelopeMoment t R y := by
  have hab : |z - y| ≤ |y| + R := (abs_sub z y).trans (by linarith)
  rw [oneDimDerivative, abs_mul, abs_neg, abs_div,
    abs_of_pos (by positivity : 0 < 2 * t), abs_of_nonneg (oneDim_nonneg _ _)]
  calc
    _ ≤ ((|y| + R) / (2 * t)) * (shiftCoefficient t R * envelopeCore t y) :=
      mul_le_mul (div_le_div_of_nonneg_right hab (by positivity))
        (oneDim_shift_le ht hR hz y) (oneDim_nonneg _ _) (by positivity)
    _ = _ := by unfold envelopeMoment; ring

theorem envelopeCore_integrable {t : ℝ} (ht : 0 < t) : Integrable (envelopeCore t) :=
  integrable_exp_neg_mul_sq (by positivity)

theorem envelopeMoment_integrable {t : ℝ} (ht : 0 < t) (R : ℝ) :
    Integrable (envelopeMoment t R) := by
  have hi : Integrable (fun y : ℝ => |y| * envelopeCore t y) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), envelopeCore]
      using (integrable_mul_exp_neg_mul_sq (by positivity : 0 < (4 * t)⁻¹ / 2)).norm
  convert! hi.add ((envelopeCore_integrable ht).mul_const R) using 1
  funext y
  dsimp only [envelopeMoment, Pi.add_apply]
  ring

/-- Operator norm of a scalar linear functional in the coordinate maximum norm. -/
theorem functional_norm_le (L : Plane →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (Pi.single 0 1)| + |L (Pi.single 1 1)| := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = v 0 • (Pi.single 0 1 : Plane) + v 1 • Pi.single 1 1 := by
    funext j
    fin_cases j <;> simp
  have he : L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [he, Real.norm_eq_abs]
  calc
    _ ≤ |v 0| * |L (Pi.single 0 1)| + |v 1| * |L (Pi.single 1 1)| := by
      simpa only [abs_mul] using abs_add_le (v 0 * L (Pi.single 0 1))
        (v 1 * L (Pi.single 1 1))
    _ ≤ ‖v‖ * |L (Pi.single 0 1)| + ‖v‖ * |L (Pi.single 1 1)| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (norm_le_pi_norm v 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_le_pi_norm v 1) (abs_nonneg _))
    _ = _ := by ring

def derivativeEnvelope (t R : ℝ) (y : Plane) : ℝ :=
  (shiftCoefficient t R ^ 2 / (2 * t)) *
    (envelopeMoment t R (y 0) * envelopeCore t (y 1) +
      envelopeCore t (y 0) * envelopeMoment t R (y 1))

private theorem integrable_product (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun y : Plane => f (y 0) * g (y 1)) := by
  have hp := hf.mul_prod hg
  exact (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable hp

theorem derivativeEnvelope_integrable {t : ℝ} (ht : 0 < t) (R : ℝ) :
    Integrable (derivativeEnvelope t R) := by
  exact ((integrable_product (envelopeMoment t R) (envelopeCore t)
    (envelopeMoment_integrable ht R) (envelopeCore_integrable ht)).add
      (integrable_product (envelopeCore t) (envelopeMoment t R)
        (envelopeCore_integrable ht) (envelopeMoment_integrable ht R))).const_mul _

theorem kernel_fderiv_shift_le {t : ℝ} (ht : 0 < t) {R : ℝ} (hR : 0 ≤ R)
    (z y : Plane) (hz : ∀ j, |z j| ≤ R) :
    ‖fderiv ℝ (kernel t) (z - y)‖ ≤ derivativeEnvelope t R y := by
  have h0 := oneDim_shift_le ht hR (hz 0) (y 0)
  have h1 := oneDim_shift_le ht hR (hz 1) (y 1)
  have hd0 := oneDimDerivative_shift_le ht hR (hz 0) (y 0)
  have hd1 := oneDimDerivative_shift_le ht hR (hz 1) (y 1)
  have ha0 : 0 ≤ shiftCoefficient t R * envelopeCore t (y 0) :=
    mul_nonneg (shiftCoefficient_nonneg t R) (le_of_lt (envelopeCore_pos t (y 0)))
  calc
    _ ≤ |kernelDerivative t 0 (z - y)| + |kernelDerivative t 1 (z - y)| := by
      simpa only [kernel_fderiv_basis ht] using functional_norm_le (fderiv ℝ (kernel t) (z - y))
    _ = |oneDimDerivative t (z 0 - y 0)| * oneDim t (z 1 - y 1) +
        oneDim t (z 0 - y 0) * |oneDimDerivative t (z 1 - y 1)| := by
      rw [kernelDerivative_zero, kernelDerivative_one]
      simp only [Pi.sub_apply, abs_mul, abs_of_nonneg (oneDim_nonneg _ _)]
    _ ≤ ((shiftCoefficient t R / (2 * t)) * envelopeMoment t R (y 0)) *
          (shiftCoefficient t R * envelopeCore t (y 1)) +
        (shiftCoefficient t R * envelopeCore t (y 0)) *
          ((shiftCoefficient t R / (2 * t)) * envelopeMoment t R (y 1)) := by
      exact add_le_add
        (mul_le_mul hd0 h1 (oneDim_nonneg _ _) ((abs_nonneg _).trans hd0))
        (mul_le_mul h0 hd1 (abs_nonneg _) ha0)
    _ = _ := by unfold derivativeEnvelope; ring

end ForcedComputation.PlaneHeat

end

end OAI
