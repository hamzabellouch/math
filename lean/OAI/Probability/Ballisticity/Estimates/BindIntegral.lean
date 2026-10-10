import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma integral_bind_nonneg_of_integrable {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (μ : Measure Ω) (Q : Ω → Measure G) (hQ : Measurable Q)
    (F : G → ℝ) (hF : Measurable F) (h0 : ∀ u, 0 ≤ F u)
    (hi : ∀ ω, Integrable F (Q ω)) :
    (∫ u, F u ∂μ.bind Q) = ∫ ω, ∫ u, F u ∂Q ω ∂μ := by
  have he (ω : Ω) : (∫ u, F u ∂Q ω) = (∫⁻ u, ENNReal.ofReal (F u) ∂Q ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hF.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hF.aestronglyMeasurable,
    Measure.lintegral_bind hQ.aemeasurable hF.ennreal_ofReal.aemeasurable]
  simp_rw [he]
  symm
  apply integral_toReal
  · exact ((Measure.measurable_lintegral (hF.ennreal_ofReal)).comp hQ).aemeasurable
  · exact Eventually.of_forall fun ω => (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mp (hi ω).hasFiniteIntegral

end DirectionalTransience

end

end

end OAI
