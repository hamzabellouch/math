import Mathlib
import OAI.Probability.SphericalField.Poisson.Palm

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma lintegral_comp_exp_all (g : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp x)*g (Real.exp x)) = ∫⁻ y : ℝ in Ioi 0, g y := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x (_ : x ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  simpa only [image_univ,Real.range_exp,Measure.restrict_univ,abs_of_pos (Real.exp_pos _)] using h.symm

lemma stableLogIntensity_laplace_moment {b r t : ℝ} (hb : 0 ≤ b) (hr : b < r) (ht : 0 < t) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)) ∂stableLogIntensity b) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)) := by
  unfold stableLogIntensity
  rw [lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  have he (x : ℝ) :
      ENNReal.ofReal (b*Real.exp (-b*x))*ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x)) =
      ENNReal.ofReal b*(ENNReal.ofReal (Real.exp x)*
        ENNReal.ofReal ((Real.exp x)^(r-b-1)*Real.exp (-t*Real.exp x))) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hb (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul hb]
    congr 1
    rw [← Real.exp_mul]
    have hx : Real.exp (-b*x)*Real.exp (r*x) = Real.exp x*Real.exp (x*(r-b-1)) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    calc
      b*Real.exp (-b*x)*(Real.exp (r*x)*Real.exp (-t*Real.exp x)) =
          b*(Real.exp (-b*x)*Real.exp (r*x))*Real.exp (-t*Real.exp x) := by ring
      _ = _ := by rw [hx]; ring
  change (∫⁻ x : ℝ, ENNReal.ofReal (b*Real.exp (-b*x))*ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))) = _
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_exp_all (fun y : ℝ => ENNReal.ofReal (y^(r-b-1)*Real.exp (-t*y))),
    show (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (y^(r-b-1)*Real.exp (-t*y))) =
      ENNReal.ofReal (t^(-(r-b))*Real.Gamma (r-b)) from by
        simpa only [neg_mul,mul_comm t] using gamma_lintegral_positive_scale (sub_pos.mpr hr) ht,
    ← ENNReal.ofReal_mul hb]
  congr 1
  rw [neg_sub]
  ring

lemma one_sub_exp_neg_lintegral {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (1-Real.exp (-u)) =
      ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (u*Real.exp (-t*u)) := by
  have hi : IntegrableOn (fun t : ℝ => u*Real.exp (-t*u)) (Ioc 0 1) :=
    (show Continuous (fun t : ℝ => u*Real.exp (-t*u)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => mul_nonneg hu.le (Real.exp_pos _).le)]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => -Real.exp (-s*u)) (u*Real.exp (-t*u)) t := by
    convert! (((hasDerivAt_id t).neg.mul_const u).exp).neg using 1
    simp only [Pi.neg_apply,id_eq,one_mul,neg_mul,mul_neg,neg_neg]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => u*Real.exp (-t*u)) by fun_prop).intervalIntegrable 0 1)]
  simp only [neg_mul,zero_mul,neg_zero,Real.exp_zero]
  ring_nf

lemma lintegral_rpow_unit {b : ℝ} (hb : 0 < b) :
    (∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (t^(b-1))) = ENNReal.ofReal b⁻¹ := by
  have hi : IntegrableOn (fun t : ℝ => t^(b-1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < b-1)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _),← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < b-1))]
  simp [Real.zero_rpow hb.ne']

lemma stableLaplaceConstant_eq_gamma {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    stableLaplaceConstant b = ENNReal.ofReal (Real.Gamma (1-b)) := by
  unfold stableLaplaceConstant
  simp_rw [one_sub_exp_neg_lintegral (Real.exp_pos _)]
  rw [lintegral_lintegral_swap (by fun_prop : Measurable (fun p : ℝ×ℝ =>
    ENNReal.ofReal (Real.exp p.1*Real.exp (-p.2*Real.exp p.1)))).aemeasurable]
  have he : (∫⁻ t : ℝ in Ioc 0 1, ∫⁻ x : ℝ,
      ENNReal.ofReal (Real.exp x*Real.exp (-t*Real.exp x)) ∂stableLogIntensity b) =
      ∫⁻ t : ℝ in Ioc 0 1, ENNReal.ofReal (b*t^(b-1)*Real.Gamma (1-b)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [one_mul] using stableLogIntensity_laplace_moment hb.le hb1 ht.1
  rw [he]
  have hG : 0 ≤ Real.Gamma (1-b) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hf (t : ℝ) : ENNReal.ofReal (b*t^(b-1)*Real.Gamma (1-b)) =
      ENNReal.ofReal (b*Real.Gamma (1-b))*ENNReal.ofReal (t^(b-1)) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hb.le hG)]
    congr 1
    ring
  simp_rw [hf]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_rpow_unit hb,
    ← ENNReal.ofReal_mul (mul_nonneg hb.le hG)]
  congr 1
  field_simp [hb.ne']

attribute [fun_prop] stablePoissonTotal_measurable

lemma stablePoissonTotal_add_dirac (x : ℝ) (η : Measure ℝ)
    (hη : (∫⁻ y, ENNReal.ofReal (Real.exp y) ∂η) ≠ ⊤) :
    stablePoissonTotal (Measure.dirac x+η) = Real.exp x+stablePoissonTotal η := by
  unfold stablePoissonTotal
  rw [lintegral_add_measure,lintegral_dirac,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hη,ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma stablePoissonTotal_laplace_lintegral {b t : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (ht : 0 < t) :
    (∫⁻ η, ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have hi : Integrable (fun η => Real.exp (-t*stablePoissonTotal η))
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
        ENNReal.toReal_nonneg)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le),
    stablePoissonTotal_laplace hb hb1 ht,stableLaplaceConstant_eq_gamma hb hb1,
    ENNReal.toReal_ofReal (Real.Gamma_pos_of_pos (by linarith)).le]

lemma stablePoisson_palm_laplace {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : b < r) (ht : 0 < t) :
    (∫⁻ η, ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal η))
      ∂η ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)*Real.exp (-Real.Gamma (1-b)*t^b)) := by
  rw [poissonRandomMeasureLaw_mecke (stableLogIntensity b) (by fun_prop : Measurable
    (fun p : Measure ℝ×ℝ => ENNReal.ofReal (Real.exp (r*p.2)*Real.exp (-t*stablePoissonTotal p.1))))]
  have he (x : ℝ) :
      (∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal (Measure.dirac x+η)))
        ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
        ENNReal.ofReal (Real.exp (-Real.Gamma (1-b)*t^b)) := by
    calc
      _ = ∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*Real.exp x))*
          ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
          ∂poissonRandomMeasureLaw (stableLogIntensity b) := by
        apply lintegral_congr_ae
        filter_upwards [stablePoisson_total_finite hb hb1] with η hη
        rw [stablePoissonTotal_add_dirac x η hη,mul_add,Real.exp_add,
          ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
        congr 1
        ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,stablePoissonTotal_laplace_lintegral hb hb1 ht]
  change (∫⁻ x, ∫⁻ η, ENNReal.ofReal (Real.exp (r*x)*Real.exp (-t*stablePoissonTotal (Measure.dirac x+η)))
        ∂poissonRandomMeasureLaw (stableLogIntensity b) ∂stableLogIntensity b) = _
  simp_rw [he]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,stableLogIntensity_laplace_moment hb.le hr ht,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hb.le (Real.rpow_nonneg ht.le _))
      (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]

lemma gamma_lintegral_rpow_scale {q b c : ℝ} (hq : -1 < q) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^q*Real.exp (-c*t^b))) =
      ENNReal.ofReal (c^(-(q+1)/b)*(1/b)*Real.Gamma ((q+1)/b)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_rpow_mul_exp_neg_mul_rpow hq hb hc) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le),
    integral_rpow_mul_exp_neg_mul_rpow hb hq hc]

def stableJumpMomentE (r : ℝ) (η : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (r*x)) ∂η

@[fun_prop] lemma stableJumpMomentE_measurable (r : ℝ) : Measurable (stableJumpMomentE r) :=
  Measure.measurable_lintegral (by fun_prop)

end SphericalPerceptron
end
end
end

end OAI
