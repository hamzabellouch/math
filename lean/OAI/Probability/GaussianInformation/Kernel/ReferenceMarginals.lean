import Mathlib
import OAI.Probability.GaussianInformation.Kernel.JointCompensation

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκfin : ∀ z w,κ z w ≠ ∞)
    (f : α × β × ι → ℝ) (hi : Integrable f (joint ν Λ K κ)) :
    (∫ t,f t ∂joint ν Λ K κ)=∫ s,∫ z,∑ w,(K z s).toReal*(κ z w).toReal*f (s,z,w) ∂Λ ∂ν := by
  have hm : Measurable (fun t : α × β × ι => K t.2.1 t.1*κ t.2.1 t.2.2) := by fun_prop
  have hfin : ∀ᵐ t ∂ν.prod (Λ.prod Measure.count),K t.2.1 t.1*κ t.2.1 t.2.2 < ∞ :=
    ae_of_all _ (fun t => ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hKfin _ _)) (lt_top_iff_ne_top.mpr (hκfin _ _)))
  have hweight : Integrable (fun t : α × β × ι =>
      (K t.2.1 t.1).toReal*(κ t.2.1 t.2.2).toReal*f t) (ν.prod (Λ.prod Measure.count)) := by
    simpa only [joint,ENNReal.toReal_mul,smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' hm hfin).mp hi
  rw [joint,integral_withDensity_eq_integral_toReal_smul hm hfin]
  simp only [ENNReal.toReal_mul,smul_eq_mul]
  rw [integral_prod _ hweight]
  apply integral_congr_ae
  filter_upwards [hweight.prod_right_ae] with s hs
  rw [integral_prod _ hs]
  congr 1
  ext z
  rw [integral_count]

lemma likelihood_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    {ε : ℝ≥0∞} (hκε : ∀ z w,ε ≤ κ z w) (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    ε ≤ ∫⁻ z,K z s*κ z w ∂Λ ∧ (∫⁻ z,K z s*κ z w ∂Λ) ≤ 1 := by
  have hm : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  constructor
  · calc
      ε = ∫⁻ z,K z s*ε ∂Λ := by rw [lintegral_mul_const _ hm,hK1,one_mul]
      _ ≤ _ := lintegral_mono (fun z => mul_le_mul_right (hκε z w) _)
  · calc
      _ ≤ ∫⁻ z,K z s*1 ∂Λ := lintegral_mono (fun z => mul_le_mul_right (hκ1 z w) _)
      _ = 1 := by simp only [mul_one,hK1]
end KernelPotential.DriftTools.FiniteReference
namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def likelihood (Λ : Measure β) (K : β → α → ℝ≥0∞)
    (κ : β → ι → ℝ≥0∞) (s : α) (w : ι) : ℝ := (∫⁻ z,K z s*κ z w ∂Λ).toReal

lemma kernel_rule_real_integrable (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    Integrable (fun z => (K z s).toReal*(κ z w).toReal) Λ := by
  have hm : Measurable (fun z => K z s*κ z w) :=
    (hK.comp (measurable_id.prodMk measurable_const)).mul
      (hκ.comp (measurable_id.prodMk measurable_const))
  have hfin : ∀ z,K z s*κ z w ≠ ∞ := fun z => ENNReal.mul_ne_top (hKfin _ _)
    (ne_of_lt ((hκ1 z w).trans_lt (by norm_num)))
  have hb := (likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hκ1 s w).2
  simpa only [ENNReal.toReal_mul] using
    (integrable_toReal_iff hm.aemeasurable (ae_of_all _ hfin)).mpr (ne_of_lt (hb.trans_lt (by norm_num)))

lemma kernel_rule_integral {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hκ1 : ∀ z w,κ z w ≤ 1) (s : α) (w : ι) :
    (∫ z,(K z s).toReal*(κ z w).toReal ∂Λ)=likelihood Λ K κ s w := by
  have hm : Measurable (fun z => K z s*κ z w) :=
    (hK.comp (measurable_id.prodMk measurable_const)).mul
      (hκ.comp (measurable_id.prodMk measurable_const))
  simpa only [likelihood,ENNReal.toReal_mul] using integral_toReal hm.aemeasurable
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (hKfin _ _)
      (ne_of_lt ((hκ1 z w).trans_lt (by norm_num))))))

lemma likelihood_measurable (Λ : Measure β) [SFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ)) :
    Measurable (Function.uncurry (likelihood Λ K κ)) := by
  apply measurable_from_prod_countable_left
  intro index
  unfold likelihood Function.uncurry
  apply Measurable.ennreal_toReal
  apply Measurable.lintegral_prod_right
  fun_prop

lemma joint_integral_signal (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (hκ1 : ∀ z,∑ w,κ z w=1)
    (f : α → ι → ℝ) (hf : Measurable (Function.uncurry f)) {M : ℝ}
    (hfM : ∀ s w,‖f s w‖ ≤ M) :
    (∫ t,f t.1 t.2.2 ∂joint ν Λ K κ)=∑ w,∫ s,likelihood Λ K κ s w*f s w ∂ν := by
  classical
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have := joint_probability ν Λ K κ hK hκ hK1 hκ1
  have hi : Integrable (fun t : α × β × ι => f t.1 t.2.2) (joint ν Λ K κ) :=
    Integrable.of_bound (hf.comp (measurable_fst.prodMk measurable_snd.snd)).aestronglyMeasurable M
      (ae_of_all _ (fun t => hfM _ _))
  rw [joint_integral ν Λ K κ hK hκ hKfin (fun z w => ne_of_lt ((hb z w).trans_lt (by norm_num))) _ hi]
  have he (s : α) :
      (∫ z,∑ w,(K z s).toReal*(κ z w).toReal*f s w ∂Λ)=∑ w,likelihood Λ K κ s w*f s w := by
    rw [integral_finsetSum _ (fun w _ => (kernel_rule_real_integrable Λ K κ hK hκ hKfin hK1 hb s w).mul_const _)]
    apply Finset.sum_congr rfl; intro w _
    rw [integral_mul_const,kernel_rule_integral Λ K κ hK hκ hKfin hb]
  simp_rw [he]
  apply integral_finsetSum
  intro w _
  have hm : Measurable (fun s => likelihood Λ K κ s w) :=
    (likelihood_measurable Λ K κ hK hκ).comp (measurable_id.prodMk measurable_const)
  have hbR (s : α) : likelihood Λ K κ s w ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by simpa using (likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hb s w).2)
  apply Integrable.of_bound (hm.mul (hf.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable M
  filter_upwards [] with s
  change ‖likelihood Λ K κ s w*f s w‖ ≤ M
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ likelihood Λ K κ s w from ENNReal.toReal_nonneg)]
  exact (mul_le_mul_of_nonneg_right (hbR s) (norm_nonneg _)).trans (by simpa using hfM s w)
end KernelPotential.DriftTools.FiniteReference

end OAI
