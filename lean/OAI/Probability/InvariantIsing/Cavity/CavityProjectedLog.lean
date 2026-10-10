import OAI.Probability.InvariantIsing.Cavity.CavityProjectedPair

namespace OAI

/-! The logarithmic normalizer under field projection and ordinary
Gaussian residual integration. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix NNReal

namespace InvariantIsing

theorem cavity_projected_log_normalizer {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν]
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hres : L.transpose * R * L = (v : ℝ) • 1)
    (y : A → EuclideanSpace ℝ (Fin d)) (hy : Measurable y) (c : ℝ)
    (hI : Integrable (fun p : Spin k × A =>
      Real.exp (fieldEnergy (cavityProjectField L (y p.2)) p.1))
      ((uniformSpinPrior k : Measure (Spin k)).prod ν)) :
    Real.log (∫ p : (A × EuclideanSpace ℝ (Fin d)) × Spin k,
      Real.exp (cavityLogFactor 0 L (c • 1) (y p.1.1 + p.1.2 :
        EuclideanSpace ℝ (Fin d)) p.2)
      ∂((ν.prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))) =
    (k : ℝ) * (c + v) / 2 +
      Real.log (∫ p : Spin k × A,
        Real.exp (fieldEnergy (cavityProjectField L (y p.2)) p.1)
        ∂((uniformSpinPrior k : Measure (Spin k)).prod ν)) := by
  let Y := fun a => cavityProjectField L (y a)
  have hY : Measurable Y := (measurable_cavityProjectField L).comp hy
  let F : (A × (Fin k → ℝ)) × Spin k → ℝ := fun p =>
    Real.exp (fieldEnergy (Y p.1.1 + p.1.2) p.2 + (k : ℝ) * c / 2)
  have hF : Measurable F := by
    have harg : Measurable (fun p : (A × (Fin k → ℝ)) × Spin k => Y p.1.1 + p.1.2) :=
      (hY.comp measurable_fst.fst).add measurable_fst.snd
    unfold F fieldEnergy
    fun_prop
  have hp := cavity_projected_spin_prior_law ν R hR L v hres
  have hproject := hp.hasLaw.integral_comp hF.aestronglyMeasurable
  have hr := cavity_spin_residual_reorder_law (N := k) ν v
  let G : (A × Spin k) × (Fin k → ℝ) → ℝ := fun p =>
    Real.exp (fieldEnergy (Y p.1.1 + p.2) p.1.2 + (k : ℝ) * c / 2)
  have hG : Measurable G := by
    have harg : Measurable (fun p : (A × Spin k) × (Fin k → ℝ) => Y p.1.1 + p.2) :=
      (hY.comp measurable_fst.fst).add measurable_snd
    unfold G fieldEnergy
    fun_prop
  have hIG : Integrable G ((ν.prod (uniformSpinPrior k)).prod (vectorGaussianLaw k v)) := by
    have hIF := cavity_residual_spin_exp_integrable ν Y hY v c hI.swap
    rw [← hr.map_eq]
    exact (integrable_map_measure hG.aestronglyMeasurable hr.measurable.aemeasurable).mpr
      (by simpa only [Function.comp_def, G, F, cavitySpinResidualReorder] using hIF)
  have he : (∫ p : (A × EuclideanSpace ℝ (Fin d)) × Spin k,
      Real.exp (cavityLogFactor 0 L (c • 1) (y p.1.1 + p.1.2 :
        EuclideanSpace ℝ (Fin d)) p.2)
      ∂((ν.prod (multivariateGaussian 0 R)).prod (uniformSpinPrior k))) =
      Real.exp ((k : ℝ) * (c + v) / 2) *
        ∫ p : Spin k × A, Real.exp (fieldEnergy (Y p.2) p.1)
          ∂((uniformSpinPrior k : Measure (Spin k)).prod ν) := by
    calc
      _ = ∫ p, F p ∂((ν.prod (vectorGaussianLaw k v)).prod (uniformSpinPrior k)) := by
        simpa only [Function.comp_def, F, Y, cavityResidualFieldProjection,
          cavity_linear_factor_project, cavityProjectField_add] using hproject
      _ = ∫ p, G p ∂((ν.prod (uniformSpinPrior k)).prod (vectorGaussianLaw k v)) :=
        hr.hasLaw.integral_comp hG.aestronglyMeasurable
      _ = _ := by
        rw [integral_prod _ hIG]
        simp only [G]
        simp_rw [cavity_residual_spin_integral, Real.exp_add]
        rw [integral_mul_const, mul_comm]
        congr 1
        exact (integral_prod_swap _).symm
  rw [he, Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos hI).ne', Real.log_exp]

end InvariantIsing

end

end OAI
