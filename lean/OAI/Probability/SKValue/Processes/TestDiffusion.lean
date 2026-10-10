import Mathlib
import OAI.Probability.SKValue.Gaussian.CoupledCoordinates
import OAI.Probability.SKValue.Evolution.BoundedSmooth
import OAI.Probability.SKValue.Equations.TestGenerator
import OAI.Probability.SKValue.Processes.TestExpectation

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma BackwardTest.diffusion_expectation {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L' Lu:ℝ} {γ:ℝ → ℝ} {u V:ℝ → ℝ → ℝ}
    (hT:0<T) (hT1:T≤1) (hu:GradientStrip T γ u K L) (h:BackwardTest T γ u V K' L')
    (hLu:0≤Lu) (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
    (∫ ω,V T (X T ω) ∂μ)=V 0 0 := by
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
  have hbound:∀ᶠ N in atTop,|(∫ ω,V T (X T ω) ∂μ)-V 0 0|≤E N+F N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have he := h.mesh_expectation hT hT1 hN
    have hf := h.coupled_terminal_error hB hT hu hXM
      (by filter_upwards [hpaths] with ω hω using hω.2.2) hN
    have ht := abs_sub_le (∫ ω,V T (X T ω) ∂μ) (A N) (V 0 0)
    change |A N-V 0 0|≤E N at he
    change |A N-(∫ ω,V T (X T ω) ∂μ)|≤F N at hf
    have hf' : |(∫ ω,V T (X T ω) ∂μ)-A N|≤F N := by
      rw [abs_sub_comm];exact hf
    linarith
  have hz := le_of_tendsto_of_tendsto tendsto_const_nhds (hE.add hF) hbound
  have habs:|(∫ ω,V T (X T ω) ∂μ)-V 0 0|=0 := le_antisymm (by simpa using hz) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)
end SKValue

end

end OAI
