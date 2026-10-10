import OAI.Analysis.CircleDomains.Topology.ScalarQuotientDescent
import OAI.Analysis.CircleDomains.Transfer.ModelProjectionFibers
import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity

namespace OAI

/-! A compact continuous target scalar constant on the actual omitted
components yields a compact continuous scalar on the source sphere. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_constant_on_fibers (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {a : Sphere → ℝ}
    (ha : ∀ p, p ∉ extendAtInfinity M.function '' G →
      ∀ q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p, a p = a q) :
    ∀ p q, M.projection p = M.projection q → a p = a q := by
  intro p q hpq
  by_cases hp : p ∈ extendAtInfinity M.function '' G
  · obtain ⟨x, hx, rfl⟩ := hp
    have hp := (inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hx).mp
      (hpq.symm.trans (M.projection_inverse x hx))
    rw [hp]
  · apply ha p hp q
    rw [← M.projection_fiber hsard hsch hG hconn hinf hTD hp]
    exact hpq.symm

 theorem compact_scalar_descent (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {v : EuclideanPlane → ℝ} (hv : Continuous v) (hvs : HasCompactSupport v)
    (hc : ∀ p, p ∉ extendAtInfinity M.function '' G →
      ∀ q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p,
        sphereFromPlaneFunction v p = sphereFromPlaneFunction v q) :
    let a := fun q => sphereFromPlaneFunction v (invFun M.projection q)
    Continuous a ∧
      HasCompactSupport (fun z : ℂ => a (z : Sphere)) ∧
      (∀ p ∈ G, a p = sphereFromPlaneFunction v (extendAtInfinity M.function p)) := by
  let a := sphereFromPlaneFunction v
  have ha : Continuous a := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ hv.continuousOn hvs.isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  have hs := M.projection_surjective hsard hsch hG hconn hinf hTD
  have hf := M.scalar_constant_on_fibers hsard hsch hG hconn hinf hTD hc
  have hi : M.projection OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using M.projection_inverse _ hinf
  have hfi : M.projection ⁻¹' {M.projection OnePoint.infty} = {OnePoint.infty} := by
    ext p
    simpa only [hi, mem_preimage, mem_singleton_iff, extendAtInfinity_infty] using
      inverse_projection_fiber_on_domain M.projection_inverse M.projection_outside hinf (y := p)
  have hz : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), a p = 0 := by
    have hsphere : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), p ∉ planeSphere '' tsupport v :=
      ((hvs.isCompact.image continuous_planeSphere).isClosed.isOpen_compl.mem_nhds (by
        rintro ⟨x, _, hx⟩
        exact OnePoint.coe_ne_infty (complexPlaneCoordinates x) hx))
    filter_upwards [hsphere] with p hp
    cases p using OnePoint.rec with
    | infty => simp [a, sphereFromPlaneFunction]
    | coe z =>
      have hvz : complexPlaneCoordinates.symm z ∉ tsupport v := by
        intro hx
        apply hp
        exact ⟨_, hx, by simp only [planeSphere, complexPlaneCoordinates.apply_symm_apply]⟩
      simpa only [a, sphereFromPlaneFunction_coe] using image_eq_zero_of_notMem_tsupport hvz
  have hzero := closed_map_zero_neighborhood_descends M.projection_closed hs hfi hz
  rw [hi] at hzero
  refine ⟨closed_map_scalar_descent_continuous M.projection_closed hs ha hf, ?_, ?_⟩
  · rw [hasCompactSupport_iff_eventuallyEq]
    exact OnePoint.tendsto_coe_infty.eventually hzero
  · intro p hp
    have hh := scalar_descent_on_projection hs hf (extendAtInfinity M.function p)
    simpa only [M.projection_inverse p hp] using hh

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
