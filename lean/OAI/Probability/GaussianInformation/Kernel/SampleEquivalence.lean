import Mathlib
import OAI.Probability.GaussianInformation.Kernel.SampleLaw

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection Projection.Support
noncomputable def samplingLaw (k d : ℕ) (η : ℝ) : Measure (Observation k d) :=
  ((gaussianRows k d).prod (gaussianRows k d)).prod ((noiseLaw k η).prod (noiseLaw k η))

noncomputable def sampleEquiv {k d : ℕ} (s : Ambient d) : Observation k d ≃ᵐ Observation k d where
  toFun t := (t.1,(projectVector t.1.1 s+t.2.1,projectVector t.1.2 s+t.2.2))
  invFun t := (t.1,(t.2.1-projectVector t.1.1 s,t.2.2-projectVector t.1.2 s))
  left_inv t := by simp
  right_inv t := by simp
  measurable_toFun := by dsimp; have hP := continuous_projectVector (k := k) (d := d); fun_prop
  measurable_invFun := by dsimp; have hP := continuous_projectVector (k := k) (d := d); fun_prop

lemma sampling_lintegral {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t,f (sampleEquiv s t) ∂samplingLaw k d η)=
      ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have hm : Measurable (fun t : Observation k d => f (sampleEquiv s t)) := hf.comp (sampleEquiv s).measurable
  rw [samplingLaw,lintegral_prod _ hm.aemeasurable,lintegral_prod]
  · apply lintegral_congr; intro X
    apply lintegral_congr; intro Z
    have hi : Measurable (fun ef : (Fin k → ℝ) × (Fin k → ℝ) =>
        f (sampleEquiv s ((X,Z),ef))) := hm.comp (measurable_const.prodMk measurable_id)
    exact lintegral_prod _ hi.aemeasurable
  · exact (Measurable.lintegral_prod_right hm).aemeasurable

attribute [local irreducible] sampleEquiv

lemma sample_measurePreserving {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    MeasurePreserving (sampleEquiv (k := k) s) (samplingLaw k d η)
      ((observationBase k d).withDensity (fun z => observationKernel η z s)) := by
  refine ⟨(sampleEquiv s).measurable,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  have hk : Measurable (fun z : Observation k d => observationKernel η z s) := by
    have hK := observationKernel_measurable (k := k) (d := d) η
    fun_prop
  calc
    _ = ∫⁻ t,f (sampleEquiv s t) ∂samplingLaw k d η := lintegral_map hf (sampleEquiv s).measurable
    _ = ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := sampling_lintegral hη s f hf
    _ = ∫⁻ z,observationKernel η z s*f z ∂observationBase k d := (observation_lintegral η hη s f hf).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul (observationBase k d) hk hf).symm

lemma sampling_probability (k d : ℕ) {η : ℝ} (hη : 0 < η) :
    IsProbabilityMeasure (samplingLaw k d η) := by
  have := noise_probability k hη
  unfold samplingLaw gaussianRows
  infer_instance

lemma observation_probability {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    IsProbabilityMeasure ((observationBase k d).withDensity (fun z => observationKernel η z s)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact observationKernel_probability hη s

lemma sample_integral {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ) :
    (∫ z,f z ∂(observationBase k d).withDensity (fun z => observationKernel η z s))=
      ∫ t,f (sampleEquiv s t) ∂samplingLaw k d η :=
  ((sample_measurePreserving hη s).integral_comp (sampleEquiv s).measurableEmbedding f).symm

lemma sample_integrable_iff {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ) :
    Integrable f ((observationBase k d).withDensity (fun z => observationKernel η z s)) ↔
      Integrable (fun t => f (sampleEquiv s t)) (samplingLaw k d η) :=
  ((sample_measurePreserving hη s).integrable_comp_emb (sampleEquiv s).measurableEmbedding).symm
end KernelPotential.Noise

end OAI
