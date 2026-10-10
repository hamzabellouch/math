import Mathlib
import OAI.Probability.SKValue.Processes.TestDiffusion
import OAI.Probability.SKValue.Equations.TestPatch
import OAI.Probability.SKValue.Evolution.TestStrip

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma SmoothTerminal.profile_diffusion_test {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (heven:∀ x,ψ (-x)=ψ x)
    (hf:BoundedSmooth f) {l:HeatProfile} (hl:l.Pairwise (fun p q ↦ p.2≤q.2))
    (hT:0<profileTime l) (hT1:profileTime l≤1)
    (hXM:∀ t∈Icc (0:ℝ) (profileTime l),AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) (profileTime l)) ∧
      IntervalIntegrable (fun s ↦ profileCoeff l s*deriv (profileValue ψ l s) (X s ω)) volume 0 (profileTime l) ∧
      (∀ t∈Icc (0:ℝ) (profileTime l),X t ω=B t.toNNReal ω+
        ∫ s in (0:ℝ)..t,profileCoeff l s*deriv (profileValue ψ l s) (X s ω)) ∧ X 0 ω=0) :
    (∫ ω,f (X (profileTime l) ω) ∂μ)=profileResponse ψ f l 0 0 := by
  have hA := hψ.profile_evolution l
  have hV := hψ.linear_profile hf l
  obtain ⟨K,L,hu⟩ := hψ.profile_gradient_strip heven hl
  obtain ⟨K',L',hv⟩ := hV.toBackwardTest (profileTime_nonneg l) hA
    (fun t _ ↦ profileCoeff_nonneg l t) (profileCoeff_mono hl)
  obtain ⟨Lu,hLu,hLip⟩ := hA.jet_joint 0
  have hLip' : ∀ s∈Icc (0:ℝ) (profileTime l),∀ t∈Icc (0:ℝ) (profileTime l),∀ x y,
      |deriv (profileValue ψ l s) x-deriv (profileValue ψ l t) y|≤Lu*(|s-t|+|x-y|) := by
    intro s hs t ht x y
    simpa only [iteratedDeriv_zero] using hLip s hs t ht y x
  have he := hv.diffusion_expectation hB hT hT1 hu hLu hLip' hXM hpaths
  rwa [profileResponse_terminal] at he
end SKValue

end

end OAI
