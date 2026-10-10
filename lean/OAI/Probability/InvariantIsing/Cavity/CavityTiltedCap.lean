import OAI.Probability.InvariantIsing.Cavity.CavityLinearGaussianMoment
import OAI.Probability.InvariantIsing.Cavity.CavityLogCap

namespace OAI

/-! The fourth tilted radial moment removes the cap from the actual
quadratic cavity exponent, uniformly over the finite-step path. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_growth_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ) (hH : Measurable H)
    (hi : Integrable (fun x => R x^4) ν) {D : ℝ} (_hD : 0 ≤ D)
    (hg : ∀ x, |H x| ≤ D * (1 + R x^2)) :
    Integrable (fun x => H x^2) ν ∧
    (∫ x, H x^2 ∂ν) ≤ 2 * D^2 * (1 + ∫ x, R x^4 ∂ν) := by
  have hb x : H x^2 ≤ 2 * D^2 * (1 + R x^4) := by
    have h := pow_le_pow_left₀ (abs_nonneg (H x)) (hg x) 2
    rw [sq_abs] at h
    nlinarith [sq_nonneg (R x^2 - 1)]
  have he : Integrable (fun x => 2 * D^2 * (1 + R x^4)) ν :=
    ((integrable_const 1).add hi).const_mul _
  have hiH : Integrable (fun x => H x^2) ν := he.mono' (hH.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb x)
  refine ⟨hiH, ?_⟩
  have h := integral_mono hiH he hb
  simpa only [integral_const_mul, integral_add (integrable_const 1) hi,
    integral_const, probReal_univ, one_smul] using h

theorem cavity_quadratic_cap_mean_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H : Ω × X → ℝ) (R : X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) (ν ω))
    (hiR : ∀ᵐ ω ∂P, Integrable (fun x => R x^4) ((ν ω).tilted (fun x => H (ω, x))))
    (hmiR : Integrable (fun ω => ∫ x, R x^4 ∂(ν ω).tilted (fun x => H (ω, x))) P)
    {D M T : ℝ} (hD : 0 ≤ D) (hT : 0 < T)
    (hg : ∀ ω x, |H (ω, x)| ≤ D * (1 + R x^2))
    (hM : (∫ ω, ∫ x, R x^4 ∂(ν ω).tilted (fun x => H (ω, x)) ∂P) ≤ M) :
    0 ≤ (∫ ω, Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
      Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) ∂P) ∧
    (∫ ω, Real.log (∫ x, Real.exp (H (ω, x)) ∂ν ω) -
      Real.log (∫ x, Real.exp (min (H (ω, x)) T) ∂ν ω) ∂P) ≤
        2 * D^2 * (1 + M) / T := by
  have hp : ∀ᵐ ω ∂P,
      Integrable (fun x => H (ω, x)^2) ((ν ω).tilted (fun x => H (ω, x))) ∧
      (∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))) ≤
        2 * D^2 * (1 + ∫ x, R x^4 ∂(ν ω).tilted (fun x => H (ω, x))) := by
    filter_upwards [he, hiR] with ω hωe hωR
    let := isProbabilityMeasure_tilted hωe
    exact cavity_growth_second_moment _ _ _ (hH.comp measurable_prodMk_left) hωR hD (hg ω)
  have henv : Integrable (fun ω =>
      2 * D^2 * (1 + ∫ x, R x^4 ∂(ν ω).tilted (fun x => H (ω, x)))) P :=
    ((integrable_const 1).add hmiR).const_mul _
  have hmi : Integrable (fun ω => ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x))) P :=
    henv.mono' (measurable_random_tilted_integral hν hH (hH.pow_const 2)).aestronglyMeasurable
      (hp.mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
        exact hω.2)
  have hK : (∫ ω, ∫ x, H (ω, x)^2 ∂(ν ω).tilted (fun x => H (ω, x)) ∂P) ≤
      2 * D^2 * (1 + M) := by
    have hh := integral_mono_ae hmi henv (hp.mono fun _ h => h.2)
    have hm := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM)
      (show 0 ≤ 2 * D^2 by positivity)
    simp only [integral_const_mul, integral_add (integrable_const 1) hmiR,
      integral_const, probReal_univ, one_smul] at hh
    exact hh.trans hm
  exact cavity_log_cap_mean_error P ν hν H hH he (hp.mono fun _ h => h.1) hmi hK hT

end InvariantIsing

end

end OAI
