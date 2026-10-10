import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws
import OAI.Combinatorics.KMedian.Probability.FiniteKernels

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]

 theorem support_map (μ : FiniteLaw Ω) (f : Ω → Ξ) (ξ : Ξ)
    (h : 0 < (μ.map f).weight ξ) : ∃ ω, 0 < μ.weight ω ∧ f ω=ξ := by
  exact μ.property_map f (fun ξ => ∃ ω, 0 < μ.weight ω ∧ f ω=ξ)
    (fun ω hω => ⟨ω,hω,rfl⟩) ξ h

end MetricKMedian.FiniteLaw
end
end

end OAI
