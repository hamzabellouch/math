import OAI.Analysis.CircleDomains.Transfer.ModelAppendedTests
import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection

namespace OAI

/-! The simultaneous selection is an admissible finite appended list,
ready for the proved scalar circle-model construction. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem FlattenedSourceSelection.compact_tests (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (hpairs : ∀ i j, i ≠ j → volume ((fun p =>
      (sphereFromPlaneFunction (u i) p,sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hsη : HasCompactSupport η)
    (hηB : ∀ z : ℂ, (z : Sphere) ∉ G → η z = 1) (hsL : tsupport η ⊆ ball 0 L)
    (θ : EuclideanPlane → ℝ) (hθ : ContDiff ℝ ∞ θ) (hsθ : HasCompactSupport θ)
    (hθA : tsupport θ ⊆ ball 0 A)
    (hθF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), θ x = 1) :
    let t := appendScalarPair (fun i => flattenValues (S.oldValues i) ∘ u i)
      (M.compactPrioritySource S.cutoff S.value η)
      (M.compactHeightSource H (flattenValues S.heightValues) θ)
    (∀ i, Continuous (t i)) ∧ (∀ i, HasCompactSupport (t i)) ∧
      Nonempty (∀ i, DeGiorgi.MemW1pWitness 2 (t i) (physicalPlaneDomain G)) ∧
      (∀ i j, i ≠ j → volume ((fun p =>
        (sphereFromPlaneFunction (t i) p,sphereFromPlaneFunction (t j) p)) '' Gᶜ) = 0) :=
  M.compact_appended_tests hsard hsch hcoarea hG hconn hinf hTD hu hs hpairs H hHz
    S.oldValues (fun i => (S.old_open i).measurableSet) S.oldWitness
    S.heightValues S.height_open.measurableSet A S.heightWitness
    S.center S.center_outside S.value S.radius S.radius_tendsto S.cutoff S.cutoff_smooth S.cutoff_support
    S.old_constant S.height_constant η hη hsη hηB hsL S.priority_continuous S.priority_error_memLp
    θ hθ hsθ hθA hθF

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
