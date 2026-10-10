import OAI.Probability.SLE.Loewner.InitialInverseEnergyBound

namespace OAI

/-! Real, integrable versions of the common inverse Dirichlet bound. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma initialInverse_energy_integrable (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) (A : ℝ) :
    IntegrableOn (fun z => ‖deriv (initialInverseChart p hi h0 hH s) z‖^2)
      (upperHalfPlane ∩ ball (0:ℂ) A) := by
  have hm : Measurable (fun z => ‖deriv (initialInverseChart p hi h0 hH s) z‖^2) :=
    (measurable_deriv _).norm.pow_const 2
  refine ⟨hm.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => sq_nonneg _))]
  exact (initialInverse_dirichlet_bound p hi h0 hH hR hp s A).trans_lt
    (isCompact_closedBall (0:ℂ) (A+3*R)).measure_lt_top

lemma initialInverse_energy_integral_le (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) (A : ℝ) :
    (∫ z in upperHalfPlane ∩ ball (0:ℂ) A,
      ‖deriv (initialInverseChart p hi h0 hH s) z‖^2)≤
        (volume (closedBall (0:ℂ) (A+3*R))).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => sq_nonneg _))
    ((measurable_deriv _).norm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono (isCompact_closedBall (0:ℂ) (A+3*R)).measure_lt_top.ne
    (initialInverse_dirichlet_bound p hi h0 hH hR hp s A)

end SLEExactGauge

end

end OAI
