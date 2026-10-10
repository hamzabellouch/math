import OAI.Analysis.AncientFlat.Spectral.ResolventCoefficients
import OAI.Analysis.AncientFlat.Kernel.GreenConvolution

namespace OAI
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace FlatRecursion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_bounded_recursion_inverse (P : E →L[ℂ] E) (q : ℝ) (hq : 0<q)
    (hcircle : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) :
    ∃ D : (ℤ →ᵇ E) →L[ℂ] (ℤ →ᵇ E), ∀ f : ℤ →ᵇ E, ∀ j : ℤ,
      (q : ℂ) • D f (j+1)=P (D f j)+f j := by
  let G := PeriodicResolvent.coeff (PeriodicResolvent.resolventLoop P q)
  exact ⟨greenOperator G, greenOperator_solves P q G
    (PeriodicResolvent.green_summable P hq hcircle)
    (PeriodicResolvent.green_identity P hq hcircle)⟩
end FlatRecursion

end

end OAI
