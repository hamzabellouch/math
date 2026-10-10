import OAI.Analysis.CircleDomains.Probability.ProbabilityMeasureEmbedding
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! Weak push-forward along an embedding reflects convergence. The proof
uses the open-set form of portmanteau and the induced topology on the point space. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma isEmbedding_probability_map
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [MetrizableSpace B] [FirstCountableTopology (ProbabilityMeasure B)]
    {f : A → B} (hf : IsEmbedding f) (hfm : MeasurableEmbedding f) :
    IsEmbedding (fun μ : ProbabilityMeasure A => μ.map f) := by
  let F : ProbabilityMeasure A → ProbabilityMeasure B := fun μ => μ.map f
  have hFc : Continuous F := ProbabilityMeasure.continuous_map hf.continuous
  apply IsEmbedding.mk' F
  · intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    exact hfm.map_injective (congrArg ProbabilityMeasure.toMeasure h)
  · intro μ
    apply le_antisymm
    · change Tendsto id (comap F (𝓝 (F μ))) (𝓝 μ)
      apply tendsto_of_forall_isOpen_le_liminf'
      intro U hU
      obtain ⟨V, hV, hVU⟩ := hf.isInducing.isOpen_iff.mp hU
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
        (show Tendsto F (comap F (𝓝 (F μ))) (𝓝 (F μ)) from tendsto_comap) hV
      simpa only [id_eq, F, ProbabilityMeasure.toMeasure_map,
        Measure.map_apply hf.continuous.measurable hV.measurableSet, hVU] using h
    · exact hFc.continuousAt.le_comap

end CircleDomainRigidity

end

end OAI
