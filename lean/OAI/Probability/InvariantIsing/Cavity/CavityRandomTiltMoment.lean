import OAI.Probability.InvariantIsing.Cavity.CavityTiltedCap
import OAI.Probability.InvariantIsing.Cavity.CavityLogCapIntegrable

namespace OAI

/-! Quadratic energy moments when the radial coordinate also depends on
the Gaussian disorder, as in the actual labeled cavity model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem cavity_random_quadratic_tilted_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hiR : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^4)
      ((ν ω).tilted (fun x => H (ω,x))))
    (hmR : Integrable (fun ω => ∫ x, R (ω,x)^4
      ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {D M : ℝ} (hD : 0 ≤ D)
    (hg : ∀ ω x, |H (ω,x)| ≤ D * (1 + R (ω,x)^2))
    (hM : (∫ ω, ∫ x, R (ω,x)^4 ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ M) :
    (∀ᵐ ω ∂P, Integrable (fun x => H (ω,x)^2)
      ((ν ω).tilted (fun x => H (ω,x)))) ∧
    Integrable (fun ω => ∫ x, H (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) P ∧
    (∫ ω, ∫ x, H (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤
      2 * D^2 * (1 + M) := by
  have hp : ∀ᵐ ω ∂P,
      Integrable (fun x => H (ω,x)^2) ((ν ω).tilted (fun x => H (ω,x))) ∧
      (∫ x, H (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) ≤
        2 * D^2 * (1 + ∫ x, R (ω,x)^4 ∂(ν ω).tilted (fun x => H (ω,x))) := by
    filter_upwards [he, hiR] with ω hωe hωR
    let := isProbabilityMeasure_tilted hωe
    exact cavity_growth_second_moment _ _ _ (hH.comp measurable_prodMk_left) hωR hD (hg ω)
  have henv : Integrable (fun ω =>
      2 * D^2 * (1 + ∫ x, R (ω,x)^4 ∂(ν ω).tilted (fun x => H (ω,x)))) P :=
    ((integrable_const 1).add hmR).const_mul _
  have hmi : Integrable (fun ω => ∫ x, H (ω,x)^2
      ∂(ν ω).tilted (fun x => H (ω,x))) P :=
    henv.mono' (measurable_random_tilted_integral hν hH (hH.pow_const 2)).aestronglyMeasurable
      (hp.mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
        exact hω.2)
  refine ⟨hp.mono (fun _ h => h.1), hmi, ?_⟩
  have hh := integral_mono_ae hmi henv (hp.mono fun _ h => h.2)
  simp only [integral_const_mul, integral_add (integrable_const 1) hmR,
    integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM)
    (by positivity))

end InvariantIsing

end

end OAI
