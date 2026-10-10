import OAI.Analysis.CircleDomains.Selection.ControlledHeightCloseness
import OAI.Analysis.CircleDomains.Topology.ModelHeightComponents

namespace OAI

/-! Uniform compact-set closeness for the actual model heights, together
with their zero gradient on the actual complement. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem uniform_near_extremal_height
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hbound : BddAbove (CompactScalarModel.coefficientSet G u))
    {R : ℝ} (hR : 0 < R) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (M : CompactScalarModel G u) d, 0 < d → d < δ →
      sSup (CompactScalarModel.coefficientSet G u)-d ≤ M.coefficient.re →
      complexPlaneCoordinates '' (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ ⊆
        ball 0 R →
      ∃ H : ControlledHeight R d,
        (∀ᵐ p ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
          heightLimitGradient H.error₀ H.error₁ p = 0) ∧
        (∀ z ∈ K, |H.height z-z.im| < ε) := by
  obtain ⟨δ, hδ, hc⟩ := controlled_heights_close (R := R) hK hε
  refine ⟨δ, hδ, ?_⟩
  intro M d hd hdδ hnear hFR
  obtain ⟨H, hz⟩ := M.exists_controlled_height hsolver hprincipal hgreen harea hinf hu hs
    hbound hd hnear hR hFR
  exact ⟨H, hz, hc d hd hdδ H⟩

end CircleDomainRigidity

end

end OAI
