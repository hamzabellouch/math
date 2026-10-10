import Mathlib
import OAI.Probability.SKSupport.Diffusion.BoundedDiffusionProperties
import OAI.Probability.SKSupport.Regularity.RightRegularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

def compactMixedGradient (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  (compactGradient W β T t x+compactGradient W γ T t x)/2

def compactMixedDrift (W : BrownianSystem Ω) (β γ : OrderParameter) (T t x : ℝ) : ℝ :=
  compactCoeff β T t*compactMixedGradient W β γ T t x

lemma compactMixedGradient_continuous (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    Continuous (fun p : ℝ × ℝ => compactMixedGradient W β γ T p.1 p.2) :=
  ((compactGradient_continuous W β hT0 hT1).add (compactGradient_continuous W γ hT0 hT1)).div_const 2

lemma compactMixedGradient_bound (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactMixedGradient W β γ T t x| ≤ 1 := by
  have hb := compactGradient_bound W β hT0 hT1 t x
  have hg := compactGradient_bound W γ hT0 hT1 t x
  unfold compactMixedGradient
  rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  linarith [abs_add_le (compactGradient W β T t x) (compactGradient W γ T t x)]

lemma compactMixedDrift_bound (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    |compactMixedDrift W β γ T t x| ≤ β.val ⟨T,⟨hT0,hT1⟩⟩ := by
  unfold compactMixedDrift
  rw [abs_mul,abs_of_nonneg (compactCoeff_bounds β hT0 hT1 t).1]
  exact (mul_le_of_le_one_right (compactCoeff_bounds β hT0 hT1 t).1
    (compactMixedGradient_bound W β γ hT0 hT1 t x)).trans (compactCoeff_bounds β hT0 hT1 t).2

lemma compactMixedDrift_lipschitz (W : BrownianSystem Ω) (β γ : OrderParameter)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (compactMixedDrift W β γ T t) := by
  obtain ⟨Lβ,hβ⟩ := compactGradient_lipschitz W β hT0 hT1
  obtain ⟨Lγ,hγ⟩ := compactGradient_lipschitz W γ hT0 hT1
  let D : ℝ≥0 := ⟨β.val ⟨T,⟨hT0,hT1⟩⟩,β.nonneg _⟩
  refine ⟨D*((Lβ+Lγ)/2),fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hsum := abs_add_le (compactGradient W β T t x-compactGradient W β T t y)
    (compactGradient W γ T t x-compactGradient W γ T t y)
  have hb := (hβ t).dist_le_mul x y
  have hg := (hγ t).dist_le_mul x y
  simp only [Real.dist_eq] at hb hg
  have hmix : |compactMixedGradient W β γ T t x-compactMixedGradient W β γ T t y| ≤
      ((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y| := by
    have he : compactMixedGradient W β γ T t x-compactMixedGradient W β γ T t y=
        ((compactGradient W β T t x-compactGradient W β T t y)+
        (compactGradient W γ T t x-compactGradient W γ T t y))/2 := by unfold compactMixedGradient;ring
    rw [he,abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    linarith
  rw [Real.dist_eq,compactMixedDrift,compactMixedDrift,← mul_sub,abs_mul,
    abs_of_nonneg (compactCoeff_bounds β hT0 hT1 t).1]
  calc
    _ ≤ compactCoeff β T t*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|) :=
      mul_le_mul_of_nonneg_left hmix (compactCoeff_bounds β hT0 hT1 t).1
    _ ≤ β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|) :=
      mul_le_mul_of_nonneg_right (compactCoeff_bounds β hT0 hT1 t).2 (by positivity)
    _ = _ := by
      change β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|)=
        ((D:ℝ)*(((Lβ:ℝ)+(Lγ:ℝ))/2))*|x-y|
      change β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2*|x-y|)=
        (β.val ⟨T,⟨hT0,hT1⟩⟩*(((Lβ:ℝ)+(Lγ:ℝ))/2))*|x-y|
      ring

def mixedStripDrift (W : BrownianSystem Ω) (β γ : OrderParameter) (T : Time) : BoundedLipschitzDrift where
  f := compactMixedDrift W β γ T
  bound := ⟨β.val T,β.nonneg T⟩
  lip := (compactMixedDrift_lipschitz W β γ T.property.1 T.property.2).choose
  measurable := ((compactCoeff_measurable β T).comp measurable_fst).mul
    (compactMixedGradient_continuous W β γ T.property.1 T.property.2).measurable
  bounded := compactMixedDrift_bound W β γ T.property.1 T.property.2
  lipschitz := (compactMixedDrift_lipschitz W β γ T.property.1 T.property.2).choose_spec

lemma mixedStripDrift_pathDrift_right (W : BrownianSystem Ω) (β γ : OrderParameter)
    (T : Time) (s : ℝ≥0) :
    ∀ᵐ ξ ∂W.law, ContinuousWithinAt (fun r => (mixedStripDrift W β γ T).pathDrift W r ξ) (Ioi (s:ℝ)) s := by
  filter_upwards [(mixedStripDrift W β γ T).solution_continuous_ae W] with ξ hξ
  have hx : Continuous (fun r : ℝ => (mixedStripDrift W β γ T).solution W.driver (Real.toNNReal r) ξ) :=
    hξ.comp (by fun_prop : Continuous Real.toNNReal)
  have hu : Continuous (fun r : ℝ => compactMixedGradient W β γ T r
      ((mixedStripDrift W β γ T).solution W.driver (Real.toNNReal r) ξ)) :=
    (compactMixedGradient_continuous W β γ T.property.1 T.property.2).comp (continuous_id.prodMk hx)
  have hh := ((compactCoeff_rightContinuous β T.property.1 T.property.2 (s:ℝ)).mono Ioi_subset_Ici_self).mul hu.continuousWithinAt
  apply hh.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [BoundedLipschitzDrift.pathDrift,mixedStripDrift,compactMixedDrift,
      Real.coe_toNNReal _ (s.coe_nonneg.trans hr.le),Pi.mul_apply]
  · simp only [BoundedLipschitzDrift.pathDrift,mixedStripDrift,compactMixedDrift,Real.toNNReal_coe,Pi.mul_apply]

end ZeroTemperatureSK

end
end

end OAI
