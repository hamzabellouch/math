import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy
import Mathlib.Algebra.QuadraticDiscriminant

namespace OAI

/-!
# Shared-angle energy and the independent-angle bound

The shell conversion uses one shared angular variable. Cauchy--Schwarz
transfers it to the positive independent-angle energy with exactly the
same endpoint symbols and radial measure.
-/

namespace Falconer
open Set MeasureTheory

theorem real_integral_product_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable (fun x => f x^2) μ) (hg : Integrable (fun x => g x^2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ) * (∫ x, g x^2 ∂μ) := by
  have hp (t : ℝ) : 0 ≤
      (∫ x, g x^2 ∂μ) * (t*t) + (-2 * ∫ x, f x * g x ∂μ) * t + ∫ x, f x^2 ∂μ := by
    have hn : (0 : ℝ) ≤ ∫ x, (f x - t*g x)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (f x - t*g x))
    have he (x : X) : (f x - t*g x)^2 =
        (t*t) * g x^2 + (-2*t) * (f x*g x) + f x^2 := by ring
    simp_rw [he] at hn
    have hadd := integral_add ((hg.const_mul (t*t)).add (hfg.const_mul (-2*t))) hf
    dsimp only [Pi.add_apply] at hadd
    rw [hadd, integral_add (hg.const_mul (t*t)) (hfg.const_mul (-2*t)),
      integral_const_mul, integral_const_mul] at hn
    nlinarith [hn]
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

theorem sphere_shared_integral_sq_le {d : ℕ} (U V : Sphere d → ℂ)
    (ψ : Sphere d → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hψb : ∀ w, |ψ w| ≤ 1)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ w, ‖U w‖ ≤ C) (hbV : ∀ w, ‖V w‖ ≤ D) :
    ‖∫ w, ψ w • (U w * star (V w)) ∂sphereMeasure d‖^2 ≤
      (∫ w, ‖U w‖^2 ∂sphereMeasure d) * (∫ w, ‖V w‖^2 ∂sphereMeasure d) := by
  have hfg : Integrable (fun w => ‖U w‖ * ‖V w‖) (sphereMeasure d) := by
    apply Integrable.of_bound (hU.norm.mul hV.norm).aestronglyMeasurable (C*D)
    filter_upwards with w
    change ‖‖U w‖ * ‖V w‖‖ ≤ C*D
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (hbU w) (hbV w) (norm_nonneg _) hC
  have hn : ‖∫ w, ψ w • (U w * star (V w)) ∂sphereMeasure d‖ ≤
      ∫ w, ‖U w‖ * ‖V w‖ ∂sphereMeasure d := by
    apply norm_integral_le_of_norm_le hfg
    filter_upwards with w
    rw [norm_smul, Real.norm_eq_abs, norm_mul, norm_star]
    exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hψb w)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (real_integral_product_sq_le (sphereMeasure d) (fun w => ‖U w‖) (fun w => ‖V w‖)
      (sphere_norm_square_integrable U hU hC hbU)
      (sphere_norm_square_integrable V hV hD hbV) hfg)

noncomputable def sharedAngularEnergy {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    (ψ : Sphere d → ℝ) (U V : ℝ × Sphere d → ℂ) : ℝ :=
  (2 : ℝ)^((d : ℝ)*(v-a)) * ∫ r,
    ‖∫ w, ψ w • (U (r,w) * star (V (r,w))) ∂sphereMeasure d‖^2
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

theorem independentAngularIntegrand_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    Integrable (fun r => sphereMoment U r * sphereMoment V r)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  apply Integrable.of_bound
    ((sphereMoment_measurable U hU).mul (sphereMoment_measurable V hV)).aestronglyMeasurable
    ((C^2 * (sphereMeasure d).real univ) * (D^2 * (sphereMeasure d).real univ))
  filter_upwards with r
  change ‖sphereMoment U r * sphereMoment V r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
  exact mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
    (sphereMoment_nonneg V r) (by positivity)

theorem sharedAngularEnergy_le_independent {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (ψ : Sphere d → ℝ) (hψ : Measurable ψ) (hψb : ∀ w, |ψ w| ≤ 1)
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    sharedAngularEnergy a v Ψ ψ U V ≤ independentAngularEnergy a v Ψ U V := by
  have hpoint (r : ℝ) :
      ‖∫ w, ψ w • (U (r,w) * star (V (r,w))) ∂sphereMeasure d‖^2 ≤
        sphereMoment U r * sphereMoment V r :=
    sphere_shared_integral_sq_le (fun w => U (r,w)) (fun w => V (r,w)) ψ
      (hU.comp (measurable_const.prodMk measurable_id))
      (hV.comp (measurable_const.prodMk measurable_id)) hψb hC hD
      (fun w => hbU (r,w)) (fun w => hbV (r,w))
  have hm : Measurable (fun r =>
      ‖∫ w, ψ w • (U (r,w) * star (V (r,w))) ∂sphereMeasure d‖^2) := by
    have hh : Measurable (fun z : ℝ × Sphere d => ψ z.2 • (U z * star (V z))) :=
      (hψ.comp measurable_snd).smul (hU.mul (continuous_star.measurable.comp hV))
    exact hh.stronglyMeasurable.integral_prod_right'.measurable.norm.pow_const 2
  have hi := independentAngularIntegrand_integrable v Ψ U V hU hV hC hD hbU hbV
  have his : Integrable (fun r =>
      ‖∫ w, ψ w • (U (r,w) * star (V (r,w))) ∂sphereMeasure d‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint r))
  exact mul_le_mul_of_nonneg_left
    (integral_mono his hi hpoint) (Real.rpow_nonneg (by norm_num) _)

end Falconer

end OAI
