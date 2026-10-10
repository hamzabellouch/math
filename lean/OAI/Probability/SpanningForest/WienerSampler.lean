import OAI.Probability.SpanningForest.GlobalWiener
import OAI.Probability.SpanningForest.UniformSampler

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.WienerSampler

abbrev Path := GlobalWiener.Path
local instance : MeasurableSpace Path := borel _
local instance : BorelSpace Path := ⟨rfl⟩

def sample : ℝ → Path :=
  Classical.choose (exists_uniform01_sampler GlobalWiener.wienerMeasure)

theorem measurable_sample : Measurable sample :=
  (Classical.choose_spec (exists_uniform01_sampler GlobalWiener.wienerMeasure)).1

theorem map_sample : uniform01.map sample = GlobalWiener.wienerMeasure :=
  (Classical.choose_spec (exists_uniform01_sampler GlobalWiener.wienerMeasure)).2

theorem hasLaw_sample : HasLaw sample GlobalWiener.wienerMeasure uniform01 :=
  ⟨measurable_sample.aemeasurable, map_sample⟩

theorem isBrownian_sample :
    IsBrownianReal (fun t u => sample u t) uniform01 := by
  constructor
  · constructor
    intro S
    exact (GlobalWiener.isBrownian_wienerMeasure.toIsPreBrownianReal.hasLaw S).comp
      hasLaw_sample
  · exact ae_of_all _ (fun u => (sample u).continuous)

def eval (u : ℝ) (t : ℝ≥0) : ℝ := sample u t

theorem measurable_eval : Measurable (fun p : ℝ × ℝ≥0 => eval p.1 p.2) :=
  continuous_eval.measurable.comp
    ((measurable_sample.comp measurable_fst).prodMk measurable_snd)

def evalReal (u t : ℝ) : ℝ := eval u (Real.toNNReal t)

theorem measurable_evalReal : Measurable (fun p : ℝ × ℝ => evalReal p.1 p.2) :=
  measurable_eval.comp
    (measurable_fst.prodMk (continuous_real_toNNReal.measurable.comp measurable_snd))

theorem continuous_eval (u : ℝ) : Continuous (eval u) := (sample u).continuous

theorem continuous_evalReal (u : ℝ) : Continuous (evalReal u) :=
  (continuous_eval u).comp continuous_real_toNNReal

@[simp] theorem evalReal_coe (u : ℝ) (t : ℝ≥0) : evalReal u t = eval u t := by
  simp [evalReal]

end Problem336.WienerSampler

end

end OAI
