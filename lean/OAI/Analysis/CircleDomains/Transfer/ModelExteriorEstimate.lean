import OAI.Analysis.CircleDomains.Uniformization.ModelUniformBounds

namespace OAI

/-! The actual normalized model retains the pointwise exterior estimate
needed on the fixed outer source collar. -/
open Set Function Filter MeasureTheory Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exterior_deviation_le (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) {R : ℝ} (hR : 0 < R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) :
    ∀ z : ℂ, 2*R ≤ ‖z‖ → ‖M.function z-z‖ ≤ R := by
  have hsub {z : ℂ} (hz : R < ‖z‖) : (z : Sphere) ∈ G := by
    apply hsource
    rintro ⟨w,hw,he⟩
    have hwz : w = z := OnePoint.coe_injective he
    subst w
    have := mem_ball_zero_iff.mp hw
    linarith
  have hf : DifferentiableOn ℂ M.function {z | R < ‖z‖} := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ (hsub hz))).differentiableWithinAt
  have hi : InjOn M.function {z | R < ‖z‖} := by
    intro z hz w hw he
    apply OnePoint.coe_injective
    apply M.conformal.bijOn.injOn (hsub hz) (hsub hw)
    simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he
  have hn : (fun z : ℂ => M.function z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using M.normalized.2
  exact harea.scaled_exterior_bound hR hf hi hn

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
