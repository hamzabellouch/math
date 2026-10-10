import OAI.Analysis.KadisonKastler.ConjugationIntegral
import OAI.Analysis.KadisonKastler.ProductStateCentralizer

namespace OAI

/-! # Scalar coefficients and equivariance of Gaussian averages -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_mul_right (Ω : H) (a b : H →L[ℂ] H)
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    productVectorState Ω (gaussianStateAverage U hU a r hr z * b) =
      ∫ t : ℝ, gaussianStateKernel r z t * productVectorState Ω (stateActionOrbit U a t * b) := by
  have hi := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) (b Ω)
  change (innerSL ℂ Ω) (∫ t, gaussianStateKernel r z t • stateActionOrbit U a t (b Ω)) = _
  rw [← (innerSL ℂ Ω).integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => inner_smul_right _ _ _

theorem gaussianStateAverage_mul_left (Ω : H) (a b : H →L[ℂ] H)
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    productVectorState Ω (b * gaussianStateAverage U hU a r hr z) =
      ∫ t : ℝ, gaussianStateKernel r z t * productVectorState Ω (b * stateActionOrbit U a t) := by
  have hi := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) Ω
  change ((innerSL ℂ Ω).comp b) (∫ t, gaussianStateKernel r z t • stateActionOrbit U a t Ω) = _
  rw [← ((innerSL ℂ Ω).comp b).integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => ((innerSL ℂ Ω).comp b).map_smul (gaussianStateKernel r z t) _

theorem gaussianStateAverage_conjugate (a : H →L[ℂ] H)
    (u : unitary (H →L[ℂ] H)) (hc : ∀ t, Commute (u : H →L[ℂ] H) (U t : H →L[ℂ] H))
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    unitaryConj u (gaussianStateAverage U hU a r hr z) =
      gaussianStateAverage U hU (unitaryConj u a) r hr z := by
  apply ContinuousLinearMap.ext
  intro x
  rw [gaussianStateAverage, unitaryConj_weightedOperatorIntegral]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [stateActionOrbit, unitaryConj_commute u _ (hc _) a]
  rfl

end

end KadisonKastler

end OAI
