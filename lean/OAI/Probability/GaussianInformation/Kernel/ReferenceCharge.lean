import Mathlib
import OAI.Probability.GaussianInformation.Kernel.BayesEnergy

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian
lemma sampling_integral_bounded {k d : ℕ} {η : ℝ} (hη : 0 < η)
    (f : Observation k d → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ t,‖f t‖ ≤ M) :
    (∫ t,f t ∂samplingLaw k d η)=∫ X,∫ Z,∫ e,∫ e',f ((X,Z),(e,e'))
      ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have := sampling_probability k d hη
  have hi := Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ hb)
    (μ := samplingLaw k d η)
  rw [samplingLaw,integral_prod _ hi]
  have hi' : Integrable (fun XZ : (Mat k d) × (Mat k d) =>
      ∫ e : (Fin k → ℝ) × (Fin k → ℝ),f (XZ,e) ∂(noiseLaw k η).prod (noiseLaw k η))
        ((gaussianRows k d).prod (gaussianRows k d)) := hi.integral_prod_left
  rw [integral_prod _ hi']
  apply integral_congr_ae
  filter_upwards [] with X
  apply integral_congr_ae
  filter_upwards [] with Z
  exact integral_prod _ (Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
    (ae_of_all _ (fun e => hb ((X,Z),e))))

lemma observationKernel_ne_top {k d : ℕ} {η : ℝ} (hη : 0 < η) (z : Observation k d) (s : Ambient d) :
    observationKernel η z s ≠ ∞ :=
  ENNReal.mul_ne_top (ne_top_of_le_ne_top (boxScale_ne_top k hη) (boxKernel_le η _ _))
    (ne_top_of_le_ne_top (boxScale_ne_top k hη) (boxKernel_le η _ _))

lemma noiseAverage_measurable {k d : ℕ} {η : ℝ} (hη : 0 < η) (φ : ((Mat k d) × (Fin k → ℝ)) → ℝ)
    (hφ : Measurable φ) (s : Ambient d) :
    Measurable (fun X : Mat k d => ∫ e,φ (X,projectVector X s+e) ∂noiseLaw k η) := by
  have hP : Measurable (fun X : Mat k d => projectVector X s) := by
    have := continuous_projectVector (k := k) (d := d)
    fun_prop
  have := noise_probability k hη
  have hm : Measurable (fun t : (Mat k d) × (Fin k → ℝ) => φ (t.1,projectVector t.1 s+t.2)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma first_rule_integral {k d : ℕ} {η : ℝ} (hη : 0 < η)
    (φ : ((Mat k d) × (Fin k → ℝ)) → ℝ) (hφ : Measurable φ)
    (hφ0 : ∀ t,0 ≤ φ t) (hφ1 : ∀ t,φ t ≤ 1) (s : Ambient d) :
    (∫ z : Observation k d,φ (z.1.1,z.2.1)
      ∂(observationBase k d).withDensity (fun z => observationKernel η z s))=
      ∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw k η ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  rw [sample_integral hη s]
  have hm : Measurable (fun t : Observation k d => φ ((sampleEquiv s t).1.1,(sampleEquiv s t).2.1)) :=
    hφ.comp (((sampleEquiv s).measurable.fst.fst).prodMk (sampleEquiv s).measurable.snd.fst)
  rw [sampling_integral_bounded hη _ hm (M := 1) (fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]; exact hφ1 _)]
  simp only [sampleEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,integral_const,probReal_univ,one_smul]
end KernelPotential.Noise

end OAI
