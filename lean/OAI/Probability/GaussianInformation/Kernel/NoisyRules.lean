import Mathlib
import OAI.Probability.GaussianInformation.Kernel.MessageComponents

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
open Projection Projection.Support GaussianTools ReferenceGaussian DriftTools.FiniteReference Bayes

lemma likelihood_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ] (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1) (s : α) :
    ∑ w,likelihood Λ K κ s w=1 := by
  have hb (z : β) (w : ι) : κ z w ≤ 1 := by
    rw [← hκ1 z]; exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ w)
  have hfin (w : ι) : (∫⁻ z,K z s*κ z w ∂Λ) ≠ ∞ :=
    ne_of_lt (((likelihood_bounds Λ K κ hK hK1 (ε := 0) (fun _ _ => bot_le) hb s w).2).trans_lt (by norm_num))
  unfold likelihood
  rw [← ENNReal.toReal_sum (fun w _ => hfin w),← lintegral_finsetSum]
  · simp only [← Finset.mul_sum,hκ1,mul_one,hK1,ENNReal.toReal_one]
  · intro w _; fun_prop

lemma likelihood_real_bounds {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (Λ : Measure β) [SigmaFinite Λ] (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1)
    {ε : ℝ} (hε : 0 ≤ ε) (hκε : ∀ z w,ENNReal.ofReal ε ≤ κ z w) (hκ1 : ∀ z w,κ z w ≤ 1)
    (s : α) (w : ι) : ε ≤ likelihood Λ K κ s w ∧ likelihood Λ K κ s w ≤ 1 := by
  obtain ⟨hl,hu⟩ := likelihood_bounds Λ K κ hK hK1 hκε hκ1 s w
  have hfin := ne_of_lt (hu.trans_lt (by norm_num : (1:ℝ≥0∞)<∞))
  exact ⟨by simpa [likelihood,ENNReal.toReal_ofReal hε] using ENNReal.toReal_mono hfin hl,
    by simpa [likelihood] using ENNReal.toReal_mono ENNReal.one_ne_top hu⟩

lemma likelihood_first {d k : ℕ} {η : ℝ} (hη : 0 < η)
    (φ : ((Mat k d) × (Fin k → ℝ)) → ℝ) (hφ : Measurable φ)
    (hφ0 : ∀ t,0 ≤ φ t) (hφ1 : ∀ t,φ t ≤ 1) (s : Ambient d) :
    ((∫⁻ z : Observation k d,observationKernel η z s*ENNReal.ofReal (φ (z.1.1,z.2.1))
      ∂observationBase k d).toReal)=
      ∫ X,∫ e,φ (X,projectVector X s+e) ∂noiseLaw k η ∂gaussianRows k d := by
  have hm : Measurable (fun z : Observation k d => φ (z.1.1,z.2.1)) :=
    hφ.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  have hK := observationKernel_measurable (k := k) (d := d) η
  have hKs : Measurable (fun z : Observation k d => observationKernel η z s) := by fun_prop
  have he := first_rule_integral hη φ hφ hφ0 hφ1 s
  rw [integral_withDensity_eq_integral_toReal_smul hKs
    (ae_of_all _ (fun z => lt_top_iff_ne_top.mpr (observationKernel_ne_top hη z s)))] at he
  have hi : Measurable (fun z : Observation k d => observationKernel η z s*ENNReal.ofReal (φ (z.1.1,z.2.1))) := by fun_prop
  rw [← integral_toReal hi.aemeasurable (ae_of_all _ (fun z => ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (observationKernel_ne_top hη z s)) ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hφ0 _),smul_eq_mul] using he

lemma log_bounded_of_bounds {α : Type*} (f : α → ℝ) {a b : ℝ} (ha : 0 < a)
    (hf : ∀ x,a ≤ f x ∧ f x ≤ b) :
    ∀ x,‖Real.log (f x)‖ ≤ |Real.log a|+|Real.log b| := by
  intro x
  rw [Real.norm_eq_abs]
  have hl := Real.log_le_log ha (hf x).1
  have hh := Real.log_le_log (ha.trans_le (hf x).1) (hf x).2
  apply abs_le.mpr
  constructor
  · have := neg_abs_le (Real.log a); have := abs_nonneg (Real.log b); linarith
  · have := le_abs_self (Real.log b); have := abs_nonneg (Real.log a); linarith

lemma referenceWeight_log_bounded {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (r : Ambient d → ℝ) (hr : Measurable r)
    {ε : ℝ} (hε : 0 < ε) (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ s,‖Real.log (referenceWeight ν r s)‖ ≤ M := by
  obtain ⟨a,b,ha,hb⟩ := referenceWeight_bounds hd ν hH hν r hr hε hrε hr1
  exact ⟨|Real.log a|+|Real.log b|,by positivity,log_bounded_of_bounds _ ha hb⟩

end KernelPotential.Noise

end OAI
