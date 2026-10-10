import OAI.Probability.InvariantIsing.Core.BoundedObservableMinimum
import OAI.Probability.IsingPerceptron.EnrichedCGF

namespace OAI

/-! A bounded random observable has a differentiable disorder-averaged CGF.
This applies to the actual temperature observable retaining common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma integrable_bounded_random_tilted_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω → X → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hB : ∀ ω x, |Y ω x| ≤ B) (t : ℝ) :
    Integrable (fun ω => ∫ x, Y ω x ∂(ν ω).tilted (fun x => t * Y ω x)) P := by
  have hm := measurable_random_tilted_integral hν (hY.const_mul t) hY
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry_apply_pair, id_eq] using bounded_tilted_integral_abs (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) t

theorem hasDerivAt_bounded_random_cgf {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X) (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (Y : Ω → X → ℝ)
    (hY : Measurable (Function.uncurry Y)) (B : ℝ) (hB : ∀ ω x, |Y ω x| ≤ B) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, cgf (Y ω) (ν ω) s ∂P)
      (∫ ω, ∫ x, Y ω x ∂(ν ω).tilted (fun x => t * Y ω x) ∂P) t := by
  apply hasDerivAt_mean_cgf ν Y
  · exact ae_of_all _ fun ω s => exp_mul_integrable_of_bound (ν ω)
      (hY.comp (measurable_const.prodMk measurable_id)) (hB ω) s
  · exact fun s => integrable_bounded_random_cgf P ν hν (Function.uncurry Y) hY B hB s
  · exact fun s => integrable_bounded_random_tilted_mean P ν hν Y hY B hB s

end InvariantIsing

end

end OAI
