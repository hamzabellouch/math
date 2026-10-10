import Mathlib
import OAI.Probability.SKValue.Equations.TestPatch
import OAI.Probability.SKValue.Evolution.TestStrip
import OAI.Probability.SKValue.Processes.EulerL1

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma SmoothTerminal.profile_weak_error {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hBrown:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {l:HeatProfile} (hl:l.Pairwise (fun p q ↦ p.2≤q.2)) {T K L Lu a b H:ℝ}
    (hTl:profileTime l=T) (hT:0<T) (hT1:T≤1) {γ:ℝ → ℝ} {u:ℝ → ℝ → ℝ}
    (hu:GradientStrip T γ u K L) (hLu:0≤Lu)
    (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,|u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (ha:0≤a) (hb:0≤b) (hH:0≤H)
    (hc:∀ t∈Icc (0:ℝ) T,profileCoeff l t≤γ t+a)
    (hs:∀ t∈Icc (0:ℝ) T,∀ x,|deriv (profileValue ψ l t) x-u t x|≤b)
    (hfl:∀ x y,|f x-f y|≤H*|x-y|)
    (hXM:∀ t∈Icc (0:ℝ) T,MemLp (X t) 2 μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) :
    |(∫ ω,f (X T ω) ∂μ)-profileResponse ψ f l 0 0|≤
      H*((∫ t in (0:ℝ)..T,γ t)-(∫ t in (0:ℝ)..T,profileCoeff l t)+T*(2*a+γ T*b))*Real.exp (T*γ T*Lu) := by
  have hA:SmoothEvolution T (profileCoeff l) (profileValue ψ l) := by simpa only [hTl] using hψ.profile_evolution l
  have hV:LinearEvolution T (profileCoeff l) (profileValue ψ l) (profileResponse ψ f l) := by
    simpa only [hTl] using hψ.linear_profile hf l
  obtain ⟨K',L',h⟩:=hV.toBackwardTest hT.le hA (fun t _ ↦ profileCoeff_nonneg l t)
    (by simpa only [hTl] using profileCoeff_mono hl)
  have hend:profileResponse ψ f l T=f := by rw [←hTl,profileResponse_terminal]
  have he:=h.diffusion_comparison hBrown hT hT1 hu hLu hLip ha hb hH hc hs
    (by simpa only [hend] using hfl) hXM hpaths
  simpa only [hend] using he
end SKValue

end

end OAI
