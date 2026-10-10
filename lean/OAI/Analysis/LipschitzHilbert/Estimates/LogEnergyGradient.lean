import OAI.Analysis.LipschitzHilbert.Estimates.LogEnergy
import Mathlib.Analysis.InnerProductSpace.NormPow

namespace OAI

/-!
# Uniform Lipschitz bound for the logarithmic-energy derivative

The dimension-free derivative bound from §9 is proved using the radial
coefficient and its one-dimensional derivative. It supplies the cancellation
between the path numerator and denominator when the path child is dominant.
-/

noncomputable section

namespace LipschitzHilbert

/-- The radial size of the logarithmic-energy gradient. -/
def radialLogSlope (p r : ℝ) : ℝ := p * r ^ (p - 1) / (1 + r ^ p)

/-- The scalar coefficient multiplying the path vector in the derivative. -/
def radialLogCoefficient (p r : ℝ) : ℝ := p * r ^ (p - 2) / (1 + r ^ p)

theorem rpow_lower_exponent_le_one_add {p r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hap : a ≤ p) : r ^ a ≤ 1 + r ^ p := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_one hr hr1 ha).trans (le_add_of_nonneg_right (Real.rpow_nonneg hr _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hap).trans
      (le_add_of_nonneg_left zero_le_one)

theorem radialLogCoefficient_nonneg {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    0 ≤ radialLogCoefficient p r := by
  unfold radialLogCoefficient
  positivity

theorem radialLogCoefficient_le {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    radialLogCoefficient p r ≤ p := by
  unfold radialLogCoefficient
  apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ p)).2
  exact mul_le_mul_of_nonneg_left
    (rpow_lower_exponent_le_one_add hr (by linarith : 0 ≤ p - 2) (by linarith))
    (by linarith)

theorem radialLogCoefficient_mul {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    radialLogCoefficient p r * r = radialLogSlope p r := by
  have hpower : r ^ (p - 2) * r = r ^ (p - 1) := by
    rw [← Real.rpow_add_one' hr (by linarith : p - 2 + 1 ≠ 0)]
    congr 1
    ring
  unfold radialLogCoefficient radialLogSlope
  rw [div_mul_eq_mul_div, mul_assoc, hpower]

theorem hasDerivAt_radialLogSlope {p r : ℝ} (hp : 4 ≤ p) (hr : 0 ≤ r) :
    HasDerivAt (radialLogSlope p)
      (p * (p - 1) * r ^ (p - 2) / (1 + r ^ p) -
        (p * r ^ (p - 1) / (1 + r ^ p)) ^ 2) r := by
  have ha := (Real.hasDerivAt_rpow_const (x := r) (p := p - 1) (Or.inr (by linarith))).const_mul p
  have hb := (Real.hasDerivAt_rpow_const (x := r) (p := p) (Or.inr (by linarith))).const_add 1
  have hd := ha.div hb (by positivity : 1 + r ^ p ≠ 0)
  convert hd using 1
  · rfl
  · field_simp
    rw [show p - 1 - 1 = p - 2 by ring]
    ring

theorem radialLogSlope_derivative_bound {p r : ℝ} (hp : 4 ≤ p) (hr : 0 ≤ r) :
    ‖deriv (radialLogSlope p) r‖ ≤ 2 * p ^ 2 := by
  rw [(hasDerivAt_radialLogSlope hp hr).deriv, Real.norm_eq_abs]
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hden : 0 < 1 + r ^ p := by positivity
  have hhigh : r ^ (p - 2) / (1 + r ^ p) ≤ 1 := by
    apply (div_le_one hden).2
    exact rpow_lower_exponent_le_one_add hr (by linarith) (by linarith)
  have hs0 : 0 ≤ p * r ^ (p - 1) / (1 + r ^ p) := by positivity
  have hs1 : p * r ^ (p - 1) / (1 + r ^ p) ≤ p := by
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left (rpow_predecessor_le_one_add (by linarith) hr) (by linarith)
  have hfirst0 : 0 ≤ p * (p - 1) * r ^ (p - 2) / (1 + r ^ p) := by positivity
  have hfirst1 : p * (p - 1) * r ^ (p - 2) / (1 + r ^ p) ≤ p * (p - 1) := by
    calc
      _ = p * (p - 1) * (r ^ (p - 2) / (1 + r ^ p)) := by ring
      _ ≤ p * (p - 1) * 1 := mul_le_mul_of_nonneg_left hhigh (by positivity)
      _ = _ := mul_one _
  have hsquare : (p * r ^ (p - 1) / (1 + r ^ p)) ^ 2 ≤ p ^ 2 :=
    sq_le_sq₀ hs0 (by linarith) |>.mpr hs1
  apply abs_le.mpr
  constructor <;> nlinarith

theorem radialLogSlope_lipschitz {p r s : ℝ} (hp : 4 ≤ p) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |radialLogSlope p r - radialLogSlope p s| ≤ 2 * p ^ 2 * |r - s| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun r hr => (hasDerivAt_radialLogSlope hp hr).differentiableAt)
    (fun r hr => radialLogSlope_derivative_bound hp hr) hs hr
  simpa only [Real.norm_eq_abs] using h

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded radial coefficient whose radial size is Lipschitz gives a
Lipschitz radial vector field. This proof never divides by a vector norm. -/
theorem radial_vector_lipschitz (k : ℝ → ℝ) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hk : ∀ r, 0 ≤ r → |k r| ≤ C)
    (hsize : ∀ r s, 0 ≤ r → 0 ≤ s → |k r * r - k s * s| ≤ L * |r - s|)
    (x y : E) : ‖k ‖x‖ • x - k ‖y‖ • y‖ ≤ (L + 2 * C) * ‖x - y‖ := by
  have hcoef : |k ‖x‖ - k ‖y‖| * ‖x‖ ≤ (L + C) * |‖x‖ - ‖y‖| := by
    calc
      _ = |(k ‖x‖ * ‖x‖ - k ‖y‖ * ‖y‖) + k ‖y‖ * (‖y‖ - ‖x‖)| := by
        have hid : (k ‖x‖ * ‖x‖ - k ‖y‖ * ‖y‖) + k ‖y‖ * (‖y‖ - ‖x‖) =
            (k ‖x‖ - k ‖y‖) * ‖x‖ := by ring
        rw [hid, abs_mul, abs_of_nonneg (norm_nonneg x)]
      _ ≤ |k ‖x‖ * ‖x‖ - k ‖y‖ * ‖y‖| + |k ‖y‖ * (‖y‖ - ‖x‖)| := abs_add_le _ _
      _ ≤ L * |‖x‖ - ‖y‖| + C * |‖x‖ - ‖y‖| := by
        rw [abs_mul, abs_sub_comm ‖y‖ ‖x‖]
        exact add_le_add (hsize _ _ (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hk _ (norm_nonneg _)) (abs_nonneg _))
      _ = _ := by ring
  have heq : k ‖x‖ • x - k ‖y‖ • y =
      k ‖y‖ • (x - y) + (k ‖x‖ - k ‖y‖) • x := by
    simp only [smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖k ‖y‖ • (x - y)‖ + ‖(k ‖x‖ - k ‖y‖) • x‖ := norm_add_le _ _
    _ = |k ‖y‖| * ‖x - y‖ + |k ‖x‖ - k ‖y‖| * ‖x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ C * ‖x - y‖ + (L + C) * |‖x‖ - ‖y‖| :=
      add_le_add (mul_le_mul_of_nonneg_right (hk _ (norm_nonneg _)) (norm_nonneg _)) hcoef
    _ ≤ C * ‖x - y‖ + (L + C) * ‖x - y‖ := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by positivity)) _
    _ = _ := by ring

end Radial

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of logarithmic energy as an actual bounded linear functional. -/
def logEnergyDerivative (p : ℝ) (x : E) : E →L[ℝ] ℝ :=
  radialLogCoefficient p ‖x‖ • innerSL ℝ x

theorem hasFDerivAt_logEnergy {p : ℝ} (hp : 1 < p) (x : E) :
    HasFDerivAt (logEnergy p) (logEnergyDerivative p x) x := by
  have h := ((hasFDerivAt_norm_rpow x hp).const_add 1).log
    (by positivity : 1 + ‖x‖ ^ p ≠ 0)
  convert h using 1
  · rfl
  · simp only [logEnergyDerivative, radialLogCoefficient, smul_smul]
    congr 1
    ring

/-- The first derivative has the sharp global bound `p`. -/
theorem norm_logEnergyDerivative_le {p : ℝ} (hp : 2 ≤ p) (x : E) :
    ‖logEnergyDerivative p x‖ ≤ p := by
  rw [logEnergyDerivative, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (radialLogCoefficient_nonneg (by linarith) (norm_nonneg x)),
    innerSL_apply_norm, radialLogCoefficient_mul hp (norm_nonneg x)]
  unfold radialLogSlope
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖x‖ ^ p)).2
  exact mul_le_mul_of_nonneg_left
    (rpow_predecessor_le_one_add (by linarith) (norm_nonneg x)) (by linarith)

/-- The global derivative is Lipschitz with a dimension-free `4 p²` constant. -/
theorem logEnergyDerivative_lipschitz {p : ℝ} (hp : 4 ≤ p) (x y : E) :
    ‖logEnergyDerivative p x - logEnergyDerivative p y‖ ≤ 4 * p ^ 2 * ‖x - y‖ := by
  have h := radial_vector_lipschitz (radialLogCoefficient p)
    (show 0 ≤ p by linarith) (show 0 ≤ 2 * p ^ 2 by positivity)
    (fun r hr => by
      rw [abs_of_nonneg (radialLogCoefficient_nonneg (by linarith) hr)]
      exact radialLogCoefficient_le (by linarith) hr)
    (fun r s hr hs => by
      rw [radialLogCoefficient_mul (by linarith) hr,
        radialLogCoefficient_mul (by linarith) hs]
      exact radialLogSlope_lipschitz hp hr hs) x y
  have heq : logEnergyDerivative p x - logEnergyDerivative p y =
      innerSL ℝ (radialLogCoefficient p ‖x‖ • x - radialLogCoefficient p ‖y‖ • y) := by
    simp only [logEnergyDerivative, map_sub, map_smul]
  rw [heq, innerSL_apply_norm]
  exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith : 2 * p ^ 2 + 2 * p ≤ 4 * p ^ 2)
    (norm_nonneg _))

end Hilbert

end LipschitzHilbert

end

end OAI
