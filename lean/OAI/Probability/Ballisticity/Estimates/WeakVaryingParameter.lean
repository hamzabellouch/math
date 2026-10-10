import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma weak_map_varying_parameter {E A B : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology E] [SecondCountableTopology A]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E) (hμ : Tendsto μ atTop (𝓝 ν))
    (a : ℕ → A) (a₀ : A) (ha : Tendsto a atTop (𝓝 a₀))
    (f : E × A → B) (hf : Continuous f) :
    Tendsto (fun i => (μ i).map (fun point => f (point, a i)))
      atTop (𝓝 (ν.map (fun point => f (point, a₀)))) := by
  have hh := (ProbabilityMeasure.continuous_map hf).tendsto (ν.prod (diracProba a₀)) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,diracProba a₀) |>.comp
      (hμ.prodMk_nhds (continuous_diracProba.tendsto a₀ |>.comp ha)))
  have hid (V : ProbabilityMeasure E) (u : A) :
      (V.prod (diracProba u)).map f =
        V.map (fun point => f (point, u)) := by
    apply Subtype.ext
    change ((V : Measure E).prod (Measure.dirac u)).map f = _
    rw [Measure.prod_dirac,Measure.map_map hf.measurable (by fun_prop)]
    rfl
  change Tendsto (fun i => ((μ i).prod (diracProba (a i))).map f)
    atTop (𝓝 ((ν.prod (diracProba a₀)).map f)) at hh
  simpa only [hid] using hh

end DirectionalTransience

end

end

end OAI
