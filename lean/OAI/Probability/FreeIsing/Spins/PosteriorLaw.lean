import OAI.Probability.FreeIsing.Gaussian.LinearSignalTilt
import OAI.Probability.FreeIsing.Spins.PosteriorTilt

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem map_cond_spin_posterior_eq_linearSignalTilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    Measure.map (mu[fun y => spinSign (S y) | mSmall])
        (ProbabilityTheory.cond mu {x | S x = a}) =
      linearSignalTilt (Measure.map (mu[fun y => spinSign (S y) | mSmall]) mu)
        id (spinSign a) := by
  let M : Ω → ℝ := mu[fun y => spinSign (S y) | mSmall]
  have hM : Measurable M := stronglyMeasurable_condExp.measurable.mono hm le_rfl
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hMb : ∀ᵐ x ∂mu, |M x| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using
      (ae_bdd_norm_condExp_of_ae_bdd_norm (m := mSmall) hSb)
  have ha : |spinSign a| ≤ 1 := by cases a <;> norm_num [spinSign]
  have hMi : Integrable M mu := integrable_condExp
  let : IsProbabilityMeasure (ProbabilityTheory.cond mu {x | S x = a}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  have hdi : Integrable (fun x => 1 + spinSign a * M x) mu :=
    (integrable_const 1).add (hMi.const_mul (spinSign a))
  let : IsFiniteMeasure (linearSignalTilt mu M (spinSign a)) :=
    isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  change Measure.map M (ProbabilityTheory.cond mu {x | S x = a}) =
    linearSignalTilt (Measure.map M mu) id (spinSign a)
  rw [← map_linearSignalTilt hM]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hM.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hM.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  have hfi : Integrable (fun x => f (M x)) mu :=
    Integrable.of_bound (f.continuous.measurable.comp hM).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (M x)))
  rw [integral_cond_spin_posterior_function hm hS f f.continuous.measurable hfi a hfair,
    integral_linearSignalTilt hM hMb ha hfi]
  rw [← integral_const_mul,
    ← integral_add hfi ((integrable_boundedSignal_mul hM hMb hfi).const_mul (spinSign a))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp [M]; ring)

end Problem367

end

end OAI
