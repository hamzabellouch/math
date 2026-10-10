import OAI.Probability.InvariantIsing.Cavity.CavityMovingCappedReplica
import OAI.Probability.InvariantIsing.Cavity.CavityUnflooredLog

namespace OAI

/-! The capped logarithm is integrable from the ordinary fourth moment.
The moment need only hold almost surely in the disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_capped_log_integrable_ae {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (H R : Ω × X → ℝ) (hH : Measurable H)
    (hi : ∀ᵐ ω ∂P, Integrable (fun x => R (ω,x)^4) (ν ω))
    (hmi : Integrable (fun ω => ∫ x, R (ω,x)^4 ∂ν ω) P)
    {D T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hg : ∀ ω x, |H (ω,x)| ≤ D * (1 + R (ω,x)^2)) :
    Integrable (fun ω => Real.log (∫ x, Real.exp (min (H (ω,x)) T) ∂ν ω)) P := by
  have hn := cavity_capped_negative_log_mean_bound_ae P ν hν H R hH hi hmi hD hT hg
    (le_refl (∫ ω, ∫ x, R (ω,x)^4 ∂ν ω ∂P))
  have hm : Measurable (fun ω => ∫ x, Real.exp (min (H (ω,x)) T) ∂ν ω) :=
    measurable_cavityWeightNormalizer ν hν _ (hH.min measurable_const).exp
  apply cavity_log_integrable_of_negative_sq P _ hm (M := Real.exp T) ?_ ?_ hn.1
  · intro ω
    apply MeasureTheory.integral_exp_pos
    apply integrable_of_measurable_abs_le (c := Real.exp T)
      ((hH.min measurable_const).exp.comp measurable_prodMk_left)
    intro x
    change |Real.exp (min (H (ω,x)) T)| ≤ Real.exp T
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (min_le_right _ _)
  · intro ω
    exact (cavityWeightNormalizer_mem (ν ω) _
      ((hH.min measurable_const).exp.comp measurable_prodMk_left) (by positivity)
      (fun x => ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩)).2

end InvariantIsing

end

end OAI
