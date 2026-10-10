import Mathlib
import OAI.Probability.SKSupport.Regularity.RightRegularity
import OAI.Probability.SKSupport.Regularity.TimeFields

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def coefficientDistance (β γ : OrderParameter) : ℝ :=
  ∫ s in (0:ℝ)..1, |extend β.val s-extend γ.val s|

lemma coefficientDistance_nonneg (β γ : OrderParameter) : 0 ≤ coefficientDistance β γ :=
  intervalIntegral.integral_nonneg (by norm_num) (fun s _ => abs_nonneg _)

lemma value_difference_bound (W : BrownianSystem Ω) (β γ : OrderParameter)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |value W β t x-value W γ t x| ≤ (3/2:ℝ)*coefficientDistance β γ := by
  apply (value_coefficient_stability W β γ t x ht1).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact intervalIntegral.integral_mono_interval ht0 ht1 le_rfl
    (Eventually.of_forall (fun s => abs_nonneg _)) ((β.integrable.sub γ.integrable).abs.intervalIntegrable)

def compactDifference (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  value W β (stripClamp T t) x-value W γ (stripClamp T t) x

def compactDifferenceRate (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactValueRate W β T t x-compactValueRate W γ T t x

lemma compactDifference_continuous (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactDifference W β γ T p.1 p.2) := by
  have hcl : ContinuousOn (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ :=
    (((continuous_stripClamp T).comp continuous_fst).prodMk continuous_snd).continuousOn
  have hm : MapsTo (fun p : ℝ × ℝ => (stripClamp T p.1,p.2)) univ
      (Icc (0:ℝ) T ×ˢ (univ : Set ℝ)) := fun p _ => ⟨stripClamp_mem hT0 p.1,mem_univ _⟩
  have hβ := (value_derivative_continuousOn W β hT0 hT1 0).comp hcl hm
  have hγ := (value_derivative_continuousOn W γ hT0 hT1 0).comp hcl hm
  exact continuousOn_univ.mp (hβ.sub hγ)

lemma compactDifference_deriv (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t : ℝ) :
    deriv (compactDifference W β γ T t)=fun x => compactGradient W β T t x-compactGradient W γ T t x := by
  funext x
  have hb := ((value_contDiff W β (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1)).differentiable (by simp) x).hasDerivAt
  have hg := ((value_contDiff W γ (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1)).differentiable (by simp) x).hasDerivAt
  exact (hb.sub hg).deriv

lemma compactDifference_family (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactDifference W β γ T) := by
  have hs (t : ℝ) : ContDiff ℝ ∞ (compactDifference W β γ T t) :=
    (value_contDiff W β (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1)).sub
      (value_contDiff W γ (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans_lt hT1))
  have hg : BoundedSmoothFamily (fun t x => compactGradient W β T t x-compactGradient W γ T t x) := by
    convert (compactGradient_family W β hT0 hT1).add ((compactGradient_family W γ hT0 hT1).const_mul (-1)) using 1
    funext t x;ring
  have hb (n : ℕ) : ∃ C : ℝ≥0, ∀ t x, |iteratedDeriv n (compactDifference W β γ T t) x| ≤ C := by
    cases n with
    | zero =>
      refine ⟨⟨(3/2:ℝ)*coefficientDistance β γ,mul_nonneg (by norm_num) (coefficientDistance_nonneg β γ)⟩,?_⟩
      intro t x
      exact value_difference_bound W β γ (stripClamp_mem hT0 t).1 ((stripClamp_mem hT0 t).2.trans hT1.le) x
    | succ n =>
      obtain ⟨C,hC⟩ := hg.bounds n
      refine ⟨C,fun t x => ?_⟩
      rw [iteratedDeriv_succ',compactDifference_deriv W β γ hT0 hT1]
      exact hC t x
  exact ⟨(compactDifference_continuous W β γ hT0 hT1).measurable,
    fun t => ⟨hs t,fun n => (hb n).imp (fun C hC x => hC t x)⟩,hb⟩

lemma compactDifferenceRate_family (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) : BoundedSmoothFamily (compactDifferenceRate W β γ T) := by
  convert (compactValueRate_family W β hT0 hT1).add ((compactValueRate_family W γ hT0 hT1).const_mul (-1)) using 1
  funext t x
  unfold compactDifferenceRate
  ring

def differenceField (W : BrownianSystem Ω) (β γ : OrderParameter) {T : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) : TimeField T where
  f := compactDifference W β γ T
  d := compactDifferenceRate W β γ T
  smooth := compactDifference_family W β γ hT0 hT1
  rate_smooth := compactDifferenceRate_family W β γ hT0 hT1
  continuous := compactDifference_continuous W β γ hT0 hT1
  rate_right := fun t x => ((compactValueRate_rightSmooth W β hT0 hT1 0 t x).mono Ioi_subset_Ici_self).sub
    ((compactValueRate_rightSmooth W γ hT0 hT1 0 t x).mono Ioi_subset_Ici_self)
  time_deriv := by
    intro t ht0 htT x
    have hd := (value_derivative_hasDerivWithinAt_right W β hT0 hT1 ht0 htT 0 x).sub
      (value_derivative_hasDerivWithinAt_right W γ hT0 hT1 ht0 htT 0 x)
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htT)] with s hs hsT
      simp only [compactDifference,stripClamp_eq ⟨ht0.trans hs.le,hsT.le⟩,iteratedDeriv_zero,Pi.sub_apply]
    · simp only [compactDifference,stripClamp_eq ⟨ht0,htT.le⟩,iteratedDeriv_zero,Pi.sub_apply]

end ZeroTemperatureSK

end
end

end OAI
