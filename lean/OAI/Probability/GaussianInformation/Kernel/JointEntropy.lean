import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ConditionalCharge

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open EntropySupport Coercivity
lemma finite_entropy_bound {N : ℕ} (hN : 0 < N) (r : Fin N → ℝ)
    (hr : ∀ w,0 ≤ r w) (h1 : ∑ w,r w=1) :
    ∑ w,-r w*Real.log (r w) ≤ Real.log (N:ℝ) := by
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hh (w : Fin N) := xlog_lower_tangent (hr w) (inv_pos.mpr hNR)
  have ht (w : Fin N) : -r w*Real.log (N:ℝ)+r w-(N:ℝ)⁻¹ ≤ r w*Real.log (r w) := by
    have h := hh w
    simp only [xlog,Real.log_inv] at h
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => ht w)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,h1] at hs
  have he : (N:ℝ)*(N:ℝ)⁻¹=1 := mul_inv_cancel₀ hNR.ne'
  rw [he] at hs
  have hn : (∑ w : Fin N,-r w*Real.log (r w))=-(∑ w : Fin N,r w*Real.log (r w)) := by
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [← Finset.sum_mul,h1,one_mul] at hs
  rw [hn]
  linarith

lemma weighted_log_ratio {N : ℕ} (r : Fin N → ℝ) (hr : ∀ w,0 < r w) (h1 : ∑ w,r w=1)
    {H : ℝ} (hH : 0 < H) :
    (∑ w,r w*Real.log (H/r w))=Real.log H+∑ w,-r w*Real.log (r w) := by
  simp_rw [Real.log_div hH.ne' (hr _).ne',mul_sub,Finset.sum_sub_distrib,
    ← Finset.sum_mul,h1,one_mul,neg_mul,Finset.sum_neg_distrib]
  ring
end KernelPotential.NoisyDrift

namespace KernelPotential.DriftTools.FiniteReference
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma joint_integral_by_message (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hKfin : ∀ z s,K z s ≠ ∞) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    (hκ1 : ∀ z,∑ w,κ z w=1)
    (f : β → ι → ℝ) (hf : Measurable (Function.uncurry f)) {M : ℝ}
    (hfM : ∀ z w,‖f z w‖ ≤ M) :
    (∫ t,f t.2.1 t.2.2 ∂joint ν Λ K κ)=
      ∑ w,∫ s,∫ z,(κ z w).toReal*f z w ∂Λ.withDensity (fun z => K z s) ∂ν := by
  classical
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have hκfin (z : β) (w : ι) : κ z w ≠ ∞ := ne_of_lt ((hb z w).trans_lt (by norm_num))
  have hκR (z : β) (w : ι) : (κ z w).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hb z w)
  have hKprob (s : α) : IsProbabilityMeasure (Λ.withDensity (fun z => K z s)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,hK1]
  have hKs (s : α) : Measurable (fun z => K z s) := hK.comp (measurable_id.prodMk measurable_const)
  have hg (w : ι) : Measurable (fun z => (κ z w).toReal*f z w) := by fun_prop
  have hgb (z : β) (w : ι) : ‖(κ z w).toReal*f z w‖ ≤ M := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    exact (mul_le_mul_of_nonneg_right (hκR z w) (norm_nonneg _)).trans (by simpa using hfM z w)
  have hgi (s : α) (w : ι) : Integrable (fun z => (κ z w).toReal*f z w) (Λ.withDensity (fun z => K z s)) := by
    have := hKprob s
    exact Integrable.of_bound (hg w).aestronglyMeasurable M (ae_of_all _ (fun z => hgb z w))
  have hzi (s : α) (w : ι) : Integrable (fun z => (K z s).toReal*(κ z w).toReal*f z w) Λ := by
    have hi := (integrable_withDensity_iff_integrable_smul' (hKs s)
      (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))).mp (hgi s w)
    simpa only [smul_eq_mul,mul_assoc] using hi
  have he (s : α) (w : ι) : (∫ z,(K z s).toReal*(κ z w).toReal*f z w ∂Λ)=
      ∫ z,(κ z w).toReal*f z w ∂Λ.withDensity (fun z => K z s) := by
    rw [integral_withDensity_eq_integral_toReal_smul (hKs s)
      (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (hKfin z s)))]
    simp only [smul_eq_mul,mul_assoc]
  have hui (w : ι) : Integrable (fun s => ∫ z,(K z s).toReal*(κ z w).toReal*f z w ∂Λ) ν := by
    have hm : Measurable (fun t : α × β => (K t.2 t.1).toReal*(κ t.2 w).toReal*f t.2 w) := by fun_prop
    apply Integrable.of_bound hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable M
    filter_upwards [] with s
    rw [he]
    have := hKprob s
    simpa using norm_integral_le_of_norm_le_const (μ := Λ.withDensity (fun z => K z s)) (ae_of_all _ (fun z => hgb z w))
  have := joint_probability ν Λ K κ hK hκ hK1 hκ1
  have hi : Integrable (fun t : α × β × ι => f t.2.1 t.2.2) (joint ν Λ K κ) :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable M (ae_of_all _ (fun t => hfM _ _))
  rw [joint_integral ν Λ K κ hK hκ hKfin hκfin _ hi]
  simp_rw [integral_finsetSum _ (fun w _ => hzi _ w)]
  rw [integral_finsetSum _ (fun w _ => hui w)]
  simp_rw [he]
end KernelPotential.DriftTools.FiniteReference

end OAI
