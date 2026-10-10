import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.QuadraticBounds

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma gaussian_exp_square_integral :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2/4)) ∂gaussianReal 0 1) =
      ENNReal.ofReal (Real.sqrt 2) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_gaussianPDF _ _).aemeasurable (by fun_prop)]
  have he (x : ℝ) : gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (x^2/4)) =
      ENNReal.ofReal (Real.sqrt 2) * gaussianPDF 0 2 x := by
    simp only [gaussianPDF, gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat,
      sub_zero, mul_one]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      mul_assoc, ← Real.exp_add]
    congr 1
    have hs : Real.sqrt (2*Real.pi*2) = Real.sqrt 2 * Real.sqrt (2*Real.pi) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    have hex : -x^2/2+x^2/4 = -x^2/(2*2) := by ring
    rw [hex, hs, mul_inv]
    field_simp
  simp only [Pi.mul_apply]
  simp_rw [he]
  rw [lintegral_const_mul _ (measurable_gaussianPDF _ _), lintegral_gaussianPDF_eq_one 0 (by norm_num), mul_one]

lemma sqrt_two_le_exp_half : Real.sqrt 2 ≤ Real.exp (1/2:ℝ) := by
  have h := Real.add_one_le_exp (1:ℝ)
  have he : (Real.exp (1/2:ℝ))^2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  nlinarith [Real.exp_pos (1/2:ℝ), Real.sqrt_nonneg (2:ℝ)]

lemma gaussian_scalar_scaled_exp_le {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 2) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp ((s*x)^2/16)) ∂gaussianReal 0 1) ≤
      ENNReal.ofReal (Real.exp (1/2:ℝ)) := by
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2/4)) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hh : s^2 ≤ 4 := by nlinarith
      have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg x)
      nlinarith
    _ = ENNReal.ofReal (Real.sqrt 2) := gaussian_exp_square_integral
    _ ≤ _ := ENNReal.ofReal_le_ofReal sqrt_two_le_exp_half

lemma stdGaussian_inner_eq_scaled {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (innerSL ℝ v) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖v‖*x) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one, innerSL_apply_norm]
  congr 1
  apply NNReal.eq
  simp only [Real.coe_toNNReal']
  simp

lemma stdGaussian_inner_exp_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((⟪v,x⟫)^2/16))
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ENNReal.ofReal (Real.exp (1/2:ℝ)) := by
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (x^2/16))) := by fun_prop
  change (∫⁻ x, ENNReal.ofReal (Real.exp (((innerSL ℝ v) x)^2/16)) ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ _
  rw [← lintegral_map hf (innerSL ℝ v).measurable, stdGaussian_inner_eq_scaled,
    lintegral_map hf (by fun_prop)]
  exact gaussian_scalar_scaled_exp_le (norm_nonneg v) hv

lemma iidGaussian_linear_exp_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    (∫⁻ x : Fin d → ℝ, ENNReal.ofReal (Real.exp ((∑ i,x i*v i)^2/16))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ ENNReal.ofReal (Real.exp (1/2:ℝ)) := by
  have h := stdGaussian_inner_exp_le v hv
  rw [← map_pi_eq_stdGaussian,lintegral_map (by fun_prop) (by fun_prop)] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, WithLp.ofLp_toLp, mul_comm] using h

lemma gaussianRows_exp_square_le {k d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    (∫⁻ X, ENNReal.ofReal (Real.exp ((∑ r,(projectVector X v r)^2)/16)) ∂gaussianRows k d) ≤
      ENNReal.ofReal (Real.exp ((k:ℝ)/2)) := by
  have hfun (X : Fin k → Fin d → ℝ) :
      ENNReal.ofReal (Real.exp ((∑ r,(projectVector X v r)^2)/16)) =
        ∏ r, ENNReal.ofReal (Real.exp ((∑ i,X r i*v i)^2/16)) := by
    rw [Finset.sum_div,Real.exp_sum,ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    rfl
  simp_rw [hfun]
  rw [gaussianRows,lintegral_pi_product (Measure.pi (fun _ : Fin d => gaussianReal 0 1))
    (fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp ((∑ i,x i*v i)^2/16))) (by fun_prop) k]
  have h := pow_le_pow_left' (iidGaussian_linear_exp_le v hv) k
  have he : ENNReal.ofReal (Real.exp (1/2:ℝ))^k = ENNReal.ofReal (Real.exp ((k:ℝ)/2)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    ring
  exact he ▸ h

lemma gaussianRows_tail {k d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 2) :
    gaussianRows k d {X | (16:ℝ)*k < ∑ r,(projectVector X v r)^2} ≤
      ENNReal.ofReal (Real.exp (-(k:ℝ)/2)) := by
  let f := fun X : Fin k → Fin d → ℝ => ENNReal.ofReal (Real.exp ((∑ r,(projectVector X v r)^2)/16))
  have hf : Measurable f := by dsimp [f,projectVector]; fun_prop
  have hsub : {X : Fin k → Fin d → ℝ | (16:ℝ)*k < ∑ r,(projectVector X v r)^2} ⊆
      {X | ENNReal.ofReal (Real.exp (k:ℝ)) ≤ f X} := by
    intro X hx
    change (16:ℝ)*k < ∑ r,(projectVector X v r)^2 at hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hm := meas_ge_le_lintegral_div (μ := gaussianRows k d) hf.aemeasurable
    (by positivity : ENNReal.ofReal (Real.exp (k:ℝ)) ≠ 0) ENNReal.ofReal_ne_top
  have hbound := ENNReal.div_le_div_right (gaussianRows_exp_square_le (k := k) v hv) (ENNReal.ofReal (Real.exp (k:ℝ)))
  have he : ENNReal.ofReal (Real.exp ((k:ℝ)/2))/ENNReal.ofReal (Real.exp (k:ℝ)) =
      ENNReal.ofReal (Real.exp (-(k:ℝ)/2)) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _),← Real.exp_sub]
    congr 2
    ring
  exact (measure_mono hsub).trans (hm.trans (he ▸ hbound))

end RepeatedLocalization

end OAI
