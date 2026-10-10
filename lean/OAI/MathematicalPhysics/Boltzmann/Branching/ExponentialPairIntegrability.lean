import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals

namespace OAI

/-! # Integrable exponential collision pairs from the common squared moment envelope -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def exponentialPair (f : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  (VelocityMoment.weight z.2.1*f (z.1,z.2.1))*(VelocityMoment.weight z.2.2*f (z.1,z.2.2))

theorem exponentialPair_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (exponentialPair f) := by
  unfold exponentialPair VelocityMoment.weight
  fun_prop

omit [MeasurableSpace X] in
theorem exponentialPair_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : X × (Velocity × Velocity)) : 0 ≤ exponentialPair f z :=
  mul_nonneg (mul_nonneg (VelocityMoment.weight_pos _).le (hf _))
    (mul_nonneg (VelocityMoment.weight_pos _).le (hf _))

theorem exponentialPair_integrable {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    {M : X → ℝ} (hMn : ∀ x, 0 ≤ M x) (hMsq : Integrable (fun x => (M x)^2) μ)
    (hbound : ∀ᵐ x ∂μ, VelocityMoment.moment (fun v => f (x,v)) ≤ ENNReal.ofReal (M x)) :
    Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hm := exponentialPair_measurable hfm
  have hn := exponentialPair_nonneg hfn
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mpr
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono_ae ?_)
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg (M x)))).mp hMsq.2)
  filter_upwards [hbound] with x hx
  have ht := VelocityMoment.moment_tensor (f := fun v => f (x,v))
    (hfm.comp (measurable_const.prodMk measurable_id))
  have he : (∫⁻ p : Velocity × Velocity, ENNReal.ofReal (exponentialPair f (x,p))) =
      VelocityMoment.moment (fun v => f (x,v))*VelocityMoment.moment (fun v => f (x,v)) := by
    simp only [exponentialPair,ENNReal.ofReal_mul
      (mul_nonneg (VelocityMoment.weight_pos _).le (hfn _))]
    exact ht
  rw [he,pow_two,ENNReal.ofReal_mul (hMn x)]
  exact mul_le_mul' hx hx

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
