import OAI.Analysis.CircleDomains.Topology.CompactHeightPullback
import OAI.Analysis.CircleDomains.Rigidity.ModelSourceTracePairs

namespace OAI

/-! The compact descended height has exactly the previously constructed
trace at every source end. Compactification does not change null-pair data. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_section_on_domain (M : CompactScalarModel G u)
    (v : EuclideanPlane → ℝ) {q : Sphere} (hq : q ∈ G) :
    sphereFromPlaneFunction v (invFun M.projection q) =
      sphereFromPlaneFunction v (extendAtInfinity M.function q) := by
  have hh : M.projection (invFun M.projection q) = q :=
    invFun_eq ⟨extendAtInfinity M.function q, M.projection_inverse q hq⟩
  exact congrArg (sphereFromPlaneFunction v)
    ((inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hq).mp hh)

 theorem compact_height_trace (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    (hη : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1)
    {q : ℂ} (hq : (q : Sphere) ∉ G) :
    sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x)))
      (invFun M.projection (q : Sphere)) = T (M.heightSection H (q : Sphere)) := by
  obtain ⟨hp, hplane, _⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hq
  let p := invFun M.projection (q : Sphere)
  have hout : complexPlaneCoordinates.symm (finiteCoord p) ∉
      physicalPlaneDomain (extendAtInfinity M.function '' G) := by
    obtain ⟨x, hx, heq⟩ := hp
    have he : complexPlaneCoordinates.symm (finiteCoord p) = x := by
      rw [← heq, complexPlaneCoordinates.symm_apply_apply]
    simpa only [he, mem_compl_iff] using hx
  change sphereFromPlaneFunction _ p = _
  change planeSphere (complexPlaneCoordinates.symm (finiteCoord p)) = p at hplane
  conv_lhs => rw [← hplane]
  simp only [planeSphere, sphereFromPlaneFunction_coe,
    hη _ hout, one_mul, complexPlaneCoordinates.apply_symm_apply, heightSection]
  rfl

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
