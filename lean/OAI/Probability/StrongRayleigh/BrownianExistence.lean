import OAI.Probability.StrongRayleigh.PreBrownianExistence
import OAI.Probability.StrongRayleigh.BrownianContinuability
import OAI.Probability.StrongRayleigh.BrownianStochasticContinuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

local instance : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def brownianRealization : (ℝ≥0 → ℝ) → C(ℝ≥0, ℝ) := fun ω =>
  DensePathExtension.extendPath dyadicTime (fun p => ω (dyadicTime p))

lemma measurable_brownianRealization : Measurable brownianRealization :=
  (DensePathExtension.measurable_extendPath dyadicTime denseRange_dyadicTime).comp
    (Measurable.of_eval (fun p => measurable_pi_apply (dyadicTime p)))

theorem isBrownianReal_brownianRealization :
    IsBrownianReal (fun t ω => brownianRealization ω t)
      (preBrownianMeasure : Measure (ℝ≥0 → ℝ)) := by
  apply BrownianStochasticContinuity.isBrownianReal_of_dense
    isPreBrownianReal_preBrownianMeasure brownianRealization
    dyadicTime denseRange_dyadicTime
  intro p
  filter_upwards [preBrownian_ae_continuable isPreBrownianReal_preBrownianMeasure] with ω hω
  exact congrFun (DensePathExtension.restrictPath_extendPath
    dyadicTime denseRange_dyadicTime hω) p

theorem exists_brownianPathMeasure :
    ∃ ν : ProbabilityMeasure C(ℝ≥0, ℝ),
      IsBrownianReal (fun t w => w t) (ν : Measure C(ℝ≥0, ℝ)) := by
  let ν := preBrownianMeasure.map brownianRealization
  refine ⟨ν, ⟨⟨fun I => ?_⟩, ae_of_all _ (fun w => w.continuous)⟩⟩
  have hm : Measurable (fun w : C(ℝ≥0, ℝ) => I.restrict (fun t => w t)) :=
    Measurable.of_eval (fun t => (continuous_eval_const (t : ℝ≥0)).measurable)
  refine ⟨hm.aemeasurable, ?_⟩
  change Measure.map _ (preBrownianMeasure.map
    brownianRealization : Measure C(ℝ≥0, ℝ)) = _
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_map hm measurable_brownianRealization]
  exact (isBrownianReal_brownianRealization.toIsPreBrownianReal.hasLaw I).map_eq

def brownianPathMeasure : ProbabilityMeasure C(ℝ≥0, ℝ) :=
  Classical.choose exists_brownianPathMeasure

theorem isBrownianReal_brownianPathMeasure :
    IsBrownianReal (fun t w => w t) (brownianPathMeasure : Measure C(ℝ≥0, ℝ)) :=
  Classical.choose_spec exists_brownianPathMeasure

theorem isPreBrownianReal_brownianPathMeasure :
    IsPreBrownianReal (fun t w => w t) (brownianPathMeasure : Measure C(ℝ≥0, ℝ)) :=
  isBrownianReal_brownianPathMeasure.toIsPreBrownianReal

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
