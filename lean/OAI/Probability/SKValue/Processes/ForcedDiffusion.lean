import Mathlib
import OAI.Probability.SKValue.Equations.ForcedGenerator
import OAI.Probability.SKValue.Processes.ForcedExpectation

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma ForcedTest.diffusion_generator_of_source_limit {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L' Lu:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (hT:0<T) (hT1:T≤1) (hu:GradientStrip T γ u K L) (h:ForcedTest T γ u V b p K' L')
    (hLu:0≤Lu) (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0)
    {I:ℝ} (hsource:Tendsto (fun N ↦ stepSize T N*∑ j∈Finset.range N,
      (∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))))
        atTop (𝓝 I)) :
    (∫ ω,V T (X T ω) ∂μ)=V 0 0+I := by
  let S := fun N ↦ stepSize T N*∑ j∈Finset.range N,
      (∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))
  let A := fun N ↦ ∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1))
  let E := fun N ↦ T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K' ((1/2+γ T)*L')+
    stepSize T N*K'*(γ T-γ 0)
  let F := fun N ↦ K'*Real.sqrt (∫ ω,(meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)
  have hδ:Tendsto (fun N:ℕ ↦ stepSize T N) atTop (𝓝 (0:ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hδ
  have hE:Tendsto E atTop (𝓝 0) := by
    simpa only [E,Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,add_zero] using
      (((hsqrt.const_mul T).mul_const (cubicEnvelopeMean (γ T) K' ((1/2+γ T)*L'))).add
        ((hδ.mul_const K').mul_const (γ T-γ 0)))
  have hF:Tendsto F atTop (𝓝 0) := by
    simpa only [F,Function.comp_def,Real.sqrt_zero,mul_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp
        (coupled_euler_L2_convergence hB hT hu hLu hLip hXM hpaths)).const_mul K')
  have hbound:∀ᶠ N in atTop,|(∫ ω,V T (X T ω) ∂μ)-V 0 0-S N|≤E N+F N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have he := h.mesh_expectation hT hT1 hN
    have hf := h.coupled_terminal_error hB hT hu hXM
      (by filter_upwards [hpaths] with ω hω using hω.2.2) hN
    have ht := abs_sub_le ((∫ ω,V T (X T ω) ∂μ)-V 0 0-S N) (A N-V 0 0-S N) 0
    change |A N-V 0 0-S N|≤E N at he
    change |A N-(∫ ω,V T (X T ω) ∂μ)|≤F N at hf
    have hf' : |(∫ ω,V T (X T ω) ∂μ)-A N|≤F N := by
      rw [abs_sub_comm];exact hf
    have hid:((∫ ω,V T (X T ω) ∂μ)-V 0 0-S N)-(A N-V 0 0-S N)=
      (∫ ω,V T (X T ω) ∂μ)-A N := by ring
    rw [hid,sub_zero,sub_zero] at ht
    linarith
  have hleft:Tendsto (fun N ↦ |(∫ ω,V T (X T ω) ∂μ)-V 0 0-S N|) atTop
      (𝓝 |(∫ ω,V T (X T ω) ∂μ)-V 0 0-I|) := (tendsto_const_nhds.sub hsource).abs
  have hz := le_of_tendsto_of_tendsto hleft (hE.add hF) hbound
  have habs:|(∫ ω,V T (X T ω) ∂μ)-V 0 0-I|=0 := le_antisymm (by simpa using hz) (abs_nonneg _)
  have he := abs_eq_zero.mp habs
  linarith
end SKValue

end

end OAI
