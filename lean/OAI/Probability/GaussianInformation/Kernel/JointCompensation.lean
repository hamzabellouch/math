import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Bayes

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace KernelPotential.DriftTools

namespace FiniteReference
variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def joint (ν : Measure α) (Λ : Measure β)
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞) : Measure (α × β × ι) :=
  (ν.prod (Λ.prod Measure.count)).withDensity (fun x => K x.2.1 x.1 * κ x.2.1 x.2.2)

lemma joint_integral_nonneg (ν : Measure α) (Λ : Measure β) [SigmaFinite ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K))
    (hκ : Measurable (Function.uncurry κ))
    (f : α × β × ι → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x,f x ∂joint ν Λ K κ) = ∫⁻ s,∫⁻ z,∑ w,K z s*κ z w*f (s,z,w) ∂Λ ∂ν := by
  rw [joint,lintegral_withDensity_eq_lintegral_mul]
  · rw [lintegral_prod]
    · apply lintegral_congr; intro s
      rw [lintegral_prod]
      · apply lintegral_congr; intro z
        simp only [lintegral_count,tsum_fintype]
        rfl
      · fun_prop
    · fun_prop
  · fun_prop
  · exact hf

lemma joint_probability (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1) :
    IsProbabilityMeasure (joint ν Λ K κ) := by
  constructor
  rw [← lintegral_one,(joint_integral_nonneg ν Λ K κ hK hκ _ measurable_const)]
  simp only [mul_one,← Finset.mul_sum,hκ1,mul_one,hK1,lintegral_one,measure_univ]

noncomputable def C (ν : Measure α) (K : β → α → ℝ≥0∞) (x : ι → α → ℝ≥0∞)
    (z : β) (w : ι) : ℝ≥0∞ := ∫⁻ s,K z s*x w s ∂ν

lemma measurable_C (ν : Measure α) [SFinite ν]
    (K : β → α → ℝ≥0∞) (x : ι → α → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hx : Measurable (Function.uncurry x)) :
    Measurable (Function.uncurry (C ν K x)) := by
  apply measurable_from_prod_countable_left
  intro index
  unfold C
  apply Measurable.lintegral_prod_right
  fun_prop

lemma joint_compensation (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hκ1 : ∀ z,∑ w,κ z w=1)
    (x : ι → α → ℝ≥0∞) (hx : Measurable (Function.uncurry x))
    (q : β → ℝ≥0∞) (hq : Measurable q) (hq1 : ∫⁻ z,q z ∂Λ=1) :
    (∫⁻ t,q t.2.1*x t.2.2 t.1/(1+C ν K x t.2.1 t.2.2) ∂joint ν Λ K κ) ≤ 1 := by
  rw [joint_integral_nonneg ν Λ K κ hK hκ]
  · have hm : Measurable (fun t : α × β => ∑ w,K t.2 t.1*κ t.2 w*
        (q t.2*x w t.1/(1+C ν K x t.2 w))) := by
      have hC := measurable_C ν K x hK hx
      fun_prop
    rw [lintegral_lintegral_swap hm.aemeasurable]
    have he : (∫⁻ z,∫⁻ s,∑ w,K z s*κ z w*(q z*x w s/(1+C ν K x z w)) ∂ν ∂Λ) =
        ∫⁻ z,∑ w,∫⁻ s,K z s*κ z w*q z*x w s/(1+C ν K x z w) ∂ν ∂Λ := by
      apply lintegral_congr; intro z
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl; intro w _
        apply lintegral_congr; intro s
        dsimp only [C]; simp only [div_eq_mul_inv]; ring
      · intro w _; fun_prop
    rw [he]
    exact compensation_lintegral ν Λ K (fun z => hK.comp (measurable_const.prodMk measurable_id))
      κ hκ1 x (fun w => hx.comp (measurable_const.prodMk measurable_id)) q hq1
  · have hC := measurable_C ν K x hK hx
    fun_prop

lemma log_comparison (ν : Measure α) (Λ : Measure β) [IsProbabilityMeasure ν] [SigmaFinite Λ]
    (K : β → α → ℝ≥0∞) (κ : β → ι → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hκ : Measurable (Function.uncurry κ))
    (hK1 : ∀ s,∫⁻ z,K z s ∂Λ=1) (hκ1 : ∀ z,∑ w,κ z w=1)
    (x : ι → α → ℝ≥0∞) (hx : Measurable (Function.uncurry x))
    (hxpos : ∀ w s,0 < x w s) (hxfin : ∀ w s,x w s ≠ ∞)
    (q : β → ℝ≥0∞) (hq : Measurable q) (hqpos : ∀ z,0 < q z)
    (hqfin : ∀ z,q z ≠ ∞) (hq1 : ∫⁻ z,q z ∂Λ=1)
    (hCfin : ∀ z w,C ν K x z w ≠ ∞)
    (hlogx : Integrable (fun t => Real.log (x t.2.2 t.1).toReal) (joint ν Λ K κ))
    (hlogq : Integrable (fun t => Real.log (q t.2.1).toReal) (joint ν Λ K κ))
    (hlogC : Integrable (fun t => Real.log (1+(C ν K x t.2.1 t.2.2).toReal)) (joint ν Λ K κ)) :
    (∫ t,Real.log (x t.2.2 t.1).toReal ∂joint ν Λ K κ) ≤
      (∫ t,Real.log (1+(C ν K x t.2.1 t.2.2).toReal) ∂joint ν Λ K κ) -
        ∫ t,Real.log (q t.2.1).toReal ∂joint ν Λ K κ := by
  have := joint_probability ν Λ K κ hK hκ hK1 hκ1
  have hC := measurable_C ν K x hK hx
  apply compensated_log_bound (joint ν Λ K κ)
    (fun t => (x t.2.2 t.1).toReal) (fun t => (q t.2.1).toReal)
    (fun t => (C ν K x t.2.1 t.2.2).toReal)
    (Filter.Eventually.of_forall (fun t => ENNReal.toReal_pos (hxpos _ _).ne' (hxfin _ _)))
    (Filter.Eventually.of_forall (fun t => ENNReal.toReal_pos (hqpos _).ne' (hqfin _)))
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    (by
      have hm : Measurable (fun t : α × β × ι => (q t.2.1).toReal*(x t.2.2 t.1).toReal /
        (1+(C ν K x t.2.1 t.2.2).toReal)) := by fun_prop
      exact hm.aestronglyMeasurable) _ hlogx hlogq hlogC
  have he (t : α × β × ι) : ENNReal.ofReal ((q t.2.1).toReal*(x t.2.2 t.1).toReal /
      (1+(C ν K x t.2.1 t.2.2).toReal)) =
      q t.2.1*x t.2.2 t.1/(1+C ν K x t.2.1 t.2.2) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hqfin _),ENNReal.ofReal_toReal (hxfin _ _),
      ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg,
      ENNReal.ofReal_one,ENNReal.ofReal_toReal (hCfin _ _)]
  simp_rw [he]
  exact joint_compensation ν Λ K κ hK hκ hκ1 x hx q hq hq1

end FiniteReference

end KernelPotential.DriftTools

end OAI
