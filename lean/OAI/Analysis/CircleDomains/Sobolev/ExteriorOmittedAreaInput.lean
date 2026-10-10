import OAI.Analysis.CircleDomains.Sobolev.TargetArea
import OAI.Analysis.CircleDomains.Modulus.PrincipalNormalization

namespace OAI

/-! Quantified numerical exterior-area bound: Ahlfors, *Conformal Invariants* (1973), Exterior Area Theorem,
Theorem 5-1, p.83. Only the omitted-area inequality for an injective
holomorphic exterior map with principal normalization is retained.
This is an explicit published-input parameter, not an axiom. -/
open Set Filter Function Metric Bornology Asymptotics
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def ExteriorOmittedAreaTheorem : Prop :=
    ∀ (F : ℂ → ℂ) (R : ℝ), 0 < R →
      DifferentiableOn ℂ F (closedBall (0 : ℂ) R)ᶜ →
      InjOn F (closedBall (0 : ℂ) R)ᶜ →
      (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹) → ExteriorOmittedAreaBound F R

end CircleDomainRigidity

end

end OAI
