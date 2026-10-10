import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ReferenceShift

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

lemma boxKernel_translate {k : ℕ} (η : ℝ) (a e : Fin k → ℝ) :
    boxKernel η a (a+e)=boxKernel η 0 e := by
  have he : a+e ∈ closedBox a η ↔ e ∈ closedBox 0 η := by
    simp [closedBox,Pi.add_apply]
  unfold boxKernel
  by_cases h : e ∈ closedBox 0 η
  · rw [Set.indicator_of_mem (he.mpr h),Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hh => h (he.mp hh)),Set.indicator_of_notMem h]

lemma lintegral_noisy_translate {k : ℕ} (η : ℝ) (a : Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y,boxKernel η a y*f y ∂volume)=∫⁻ e,f (a+e) ∂noiseLaw k η := by
  rw [noiseLaw]
  have hm : Measurable (fun e : Fin k → ℝ => f (a+e)) := hf.comp (measurable_const.add measurable_id)
  rw [lintegral_withDensity_eq_lintegral_mul volume (measurable_noise_density η) hm]
  rw [← lintegral_add_left_eq_self (fun y => boxKernel η a y*f y) a]
  simp only [Pi.mul_apply,boxKernel_translate]

abbrev Observation (k d : ℕ) :=
  ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ))
noncomputable def observationBase (k d : ℕ) : Measure (Observation k d) :=
  ((gaussianRows k d).prod (gaussianRows k d)).prod
    ((volume : Measure (Fin k → ℝ)).prod volume)
noncomputable def observationKernel {k d : ℕ} (η : ℝ) (z : Observation k d) (s : Ambient d) : ℝ≥0∞ :=
  boxKernel η (projectVector z.1.1 s) z.2.1*boxKernel η (projectVector z.1.2 s) z.2.2

instance observationBase_sigmaFinite (k d : ℕ) : SigmaFinite (observationBase k d) := by
  unfold observationBase gaussianRows
  infer_instance

lemma observationKernel_measurable {k d : ℕ} (η : ℝ) :
    Measurable (Function.uncurry (observationKernel (k := k) (d := d) η)) := by
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  unfold observationKernel Function.uncurry
  fun_prop

lemma observationKernel_probability {k d : ℕ} {η : ℝ} (hη : 0 < η) (s : Ambient d) :
    (∫⁻ z,observationKernel (k := k) η z s ∂observationBase k d)=1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  rw [observationBase,lintegral_prod _ (by
    exact ((observationKernel_measurable η).comp (measurable_id.prodMk measurable_const)).aemeasurable)]
  have inner (X Z : Fin k → Fin d → ℝ) :
      (∫⁻ yz : (Fin k → ℝ) × (Fin k → ℝ),
        boxKernel η (projectVector X s) yz.1*boxKernel η (projectVector Z s) yz.2
        ∂(volume : Measure (Fin k → ℝ)).prod volume)=1 := by
    have hm (c : Fin k → ℝ) : Measurable (boxKernel η c) :=
      (measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod_mul (hm _).aemeasurable (hm _).aemeasurable,
      lintegral_boxKernel η hη,lintegral_boxKernel η hη,one_mul]
  simp only [observationKernel,inner,lintegral_one,measure_univ]

lemma observation_lintegral {k d : ℕ} (η : ℝ) (hη : 0 < η) (s : Ambient d)
    (f : Observation k d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,observationKernel η z s*f z ∂observationBase k d)=
      ∫⁻ X,∫⁻ Z,∫⁻ e,∫⁻ e',f ((X,Z),(projectVector X s+e,projectVector Z s+e'))
        ∂noiseLaw k η ∂noiseLaw k η ∂gaussianRows k d ∂gaussianRows k d := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have := noise_probability k hη
  have hM : Measurable (fun z : Observation k d => observationKernel η z s*f z) :=
    ((observationKernel_measurable η).comp (measurable_id.prodMk measurable_const)).mul hf
  rw [observationBase,lintegral_prod _ hM.aemeasurable,lintegral_prod]
  · apply lintegral_congr; intro X
    apply lintegral_congr; intro Z
    have hz : Measurable (fun yz : (Fin k → ℝ) × (Fin k → ℝ) =>
        observationKernel η ((X,Z),yz) s*f ((X,Z),yz)) :=
      hM.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_prod _ hz.aemeasurable]
    dsimp only [observationKernel]
    have hinside (y : Fin k → ℝ) :
        (∫⁻ z,boxKernel η (projectVector X s) y*boxKernel η (projectVector Z s) z*f ((X,Z),(y,z)))=
          boxKernel η (projectVector X s) y*(∫⁻ e',f ((X,Z),(y,projectVector Z s+e')) ∂noiseLaw k η) := by
      simp_rw [mul_assoc]
      rw [lintegral_const_mul]
      · congr 1
        exact lintegral_noisy_translate η (projectVector Z s) (fun z => f ((X,Z),(y,z)))
          (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      · exact ((measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)).mul
          (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
    simp_rw [hinside]
    apply lintegral_noisy_translate
    have hi : Measurable (fun yz : (Fin k → ℝ) × (Fin k → ℝ) =>
        f ((X,Z),(yz.1,projectVector Z s+yz.2))) := by fun_prop
    exact Measurable.lintegral_prod_right hi
  · exact (Measurable.lintegral_prod_right hM).aemeasurable

end KernelPotential.Noise

end OAI
