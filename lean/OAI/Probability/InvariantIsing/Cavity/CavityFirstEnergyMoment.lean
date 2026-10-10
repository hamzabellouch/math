import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCapFirstMoment

namespace OAI

/-! A quadratic spatial bound needs only the second tilted radial moment
when removing the cap from bounded spin tests. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_growth_first_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H R : X → ℝ) (hH : Measurable H)
    (hi : Integrable (fun x => R x^2) ν) {D : ℝ}
    (hg : ∀ x, |H x| ≤ D * (1 + R x^2)) :
    Integrable (fun x => |H x|) ν ∧
    (∫ x, |H x| ∂ν) ≤ D * (1 + ∫ x, R x^2 ∂ν) := by
  have he : Integrable (fun x => D * (1 + R x^2)) ν :=
    ((integrable_const 1).add hi).const_mul _
  have hI : Integrable (fun x => |H x|) ν := he.mono' hH.abs.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hg x)
  refine ⟨hI, ?_⟩
  have h := integral_mono hI he hg
  simpa only [integral_const_mul, integral_add (integrable_const 1) hi,
    integral_const, probReal_univ, one_smul] using h

theorem cavity_random_first_energy_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) (ν ω))
    (hiR : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^2) ((ν ω).tilted (fun x => H (ω,x))))
    (hmiR : Integrable (fun ω => ∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) P)
    {D M : ℝ} (hD : 0 ≤ D)
    (hg : ∀ ω x, |H (ω,x)| ≤ D * (1 + R (ω,x)^2))
    (hM : (∫ ω, ∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ M) :
    (∀ᵐ ω ∂P, Integrable (fun x => |H (ω,x)|) ((ν ω).tilted (fun x => H (ω,x)))) ∧
    Integrable (fun ω => ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) P ∧
    (∫ ω, ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x)) ∂P) ≤ D * (1 + M) := by
  have hp : ∀ᵐ ω ∂P,
      Integrable (fun x => |H (ω,x)|) ((ν ω).tilted (fun x => H (ω,x))) ∧
      (∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) ≤
        D * (1 + ∫ x, R (ω,x)^2 ∂(ν ω).tilted (fun x => H (ω,x))) := by
    filter_upwards [he, hiR] with ω heω hiω
    let := isProbabilityMeasure_tilted heω
    exact cavity_growth_first_moment _ _ _ (hH.comp measurable_prodMk_left) hiω (hg ω)
  have henv : Integrable (fun ω => D * (1 + ∫ x, R (ω,x)^2
      ∂(ν ω).tilted (fun x => H (ω,x)))) P :=
    ((integrable_const 1).add hmiR).const_mul D
  have hmi : Integrable (fun ω => ∫ x, |H (ω,x)| ∂(ν ω).tilted (fun x => H (ω,x))) P :=
    henv.mono' (measurable_random_tilted_integral hν hH hH.abs).aestronglyMeasurable
      (hp.mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
        exact hω.2)
  refine ⟨hp.mono (fun _ h => h.1), hmi, ?_⟩
  have hh := integral_mono_ae hmi henv (hp.mono fun _ h => h.2)
  simp only [integral_const_mul, integral_add (integrable_const 1) hmiR,
    integral_const, probReal_univ, one_smul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hM) hD)

end InvariantIsing

end

end OAI
