import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicRenormalizedCompactness

namespace OAI

/-! # The nonnegative entropy marginal and its finite-entropy interpretation -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

def entropyMarginal (F : ℝ × Phase → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (F (t,p)))

theorem entropyMarginal_measurable {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (entropyMarginal F) :=
  (spacetimeRelativeEntropy_measurable hF).ennreal_ofReal.lintegral_prod_right'

theorem scalarRelativeEntropy_integrable {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Integrable (fun p => scalarRelativeEntropy (maxwellian p.2) (f p)) := by
  apply ((hi.const_mul initialEntropyCoefficient).add integrable_maxwellian_phase).mono'
    (scalarRelativeEntropy_measurable (by unfold maxwellian; fun_prop) hfm).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hf p))]
  exact relativeEntropy_density_bound hf p

theorem entropyMarginal_eq {F : ℝ × Phase → ℝ} (hF : Measurable F) (hFn : ∀ z, 0 ≤ F z)
    (t : ℝ) (hi : Integrable (entropyMoment (fun p => F (t,p)))) :
    entropyMarginal F t = ENNReal.ofReal (relativeEntropy (fun p => F (t,p))) := by
  have hh := scalarRelativeEntropy_integrable (f := fun p => F (t,p))
    (hF.comp (measurable_const.prodMk measurable_id)) (fun p => hFn (t,p)) hi
  rw [entropyMarginal,← ofReal_integral_eq_lintegral_ofReal hh
    (ae_of_all _ (fun p => scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hFn (t,p))))]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
