import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoisyReference

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_observation_lintegral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hκ1 : ∀ z,∑ w,κ z w=1) (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t,f (t.1,t.2.1) ∂joint ν Λ K κ)=∫⁻ s,∫⁻ z,K z s*f (s,z) ∂Λ ∂ν := by
  have hm : Measurable (fun t : α × β × ι => f (t.1,t.2.1)) :=
    hf.comp (measurable_fst.prodMk measurable_snd.fst)
  rw [joint_integral_nonneg ν Λ K κ hK hκ _ hm]
  apply lintegral_congr; intro s
  apply lintegral_congr; intro z
  change (∑ w,K z s*κ z w*f (s,z))=_
  rw [← Finset.sum_mul,← Finset.mul_sum,hκ1,mul_one]

lemma joint_observation_integrable (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hκ1 : ∀ z,∑ w,κ z w=1) (f : α × β → ℝ) (hf : Measurable f)
    (hi : (∫⁻ s,∫⁻ z,K z s*‖f (s,z)‖ₑ ∂Λ ∂ν)<∞) :
    Integrable (fun t => f (t.1,t.2.1)) (joint ν Λ K κ) := by
  refine ⟨(hf.comp (measurable_fst.prodMk measurable_snd.fst)).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm,joint_observation_lintegral ν Λ K κ hK hκ hκ1 _ hf.enorm]
  exact hi

lemma joint_observation_integral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκ1 : ∀ z,∑ w,κ z w=1)
    (f : α × β → ℝ) (hi : Integrable (fun t => f (t.1,t.2.1)) (joint ν Λ K κ)) :
    (∫ t,f (t.1,t.2.1) ∂joint ν Λ K κ)=∫ s,∫ z,f (s,z) ∂Λ.withDensity (fun z => K z s) ∂ν := by
  classical
  have hκfin (z : β) (w : ι) : κ z w ≠ ∞ := by
    have hb : κ z w ≤ 1 := by rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
    exact ne_of_lt (hb.trans_lt (by norm_num))
  have hκR (z : β) : ∑ w,(κ z w).toReal=1 := by
    rw [← ENNReal.toReal_sum (fun w _ => hκfin z w),hκ1,ENNReal.toReal_one]
  rw [joint_integral ν Λ K κ hK hκ hKfin hκfin _ hi]
  apply integral_congr_ae
  filter_upwards [] with s
  have hKs : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  rw [integral_withDensity_eq_integral_toReal_smul hKs
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [smul_eq_mul]
  rw [← Finset.sum_mul,← Finset.mul_sum,hκR,mul_one]
end KernelPotential.DriftTools.FiniteReference

end OAI
