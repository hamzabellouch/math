import OAI.Analysis.CircleDomains.Topology.ProperBoundaryApproach
import OAI.Analysis.CircleDomains.Uniformization.PrincipalJordanCircleMap
import OAI.Analysis.CircleDomains.Topology.SphereJordanCoordinates
import OAI.Analysis.CircleDomains.Transfer.SourceAnchor

namespace OAI

/-! Boundary modulus limits for actual spherical conformal equivalences.
Only the interior equivalence is assumed. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma IsConformalEquivalence.tendsto_frontier {f : Sphere → Sphere}
    {U V : Set Sphere} (hf : IsConformalEquivalence f U V) (hV : IsOpen V)
    {p : Sphere} (hp : p∉U) : Tendsto f (𝓝[U] p) (𝓝ˢ (frontier V)) := by
  obtain ⟨_,hm,fi,hic,him,hl,_⟩ := hf
  exact tendsto_frontier_of_inverse hV hm him (fun y hy => (hic y hy).1.continuousWithinAt) hl hp

lemma continuousAt_finiteCoord_of_ne_infty {p : Sphere} (hp : p≠∞) :
    ContinuousAt finiteCoord p :=
  (continuousOn_finiteCoord_of_avoids_infty (S := {∞}ᶜ) (by simp)).continuousAt
    (isOpen_compl_singleton.mem_nhds hp)

lemma frontier_sphere_ball (c : ℂ) {r : ℝ} (hr : 0<r) :
    frontier (((↑) : ℂ → Sphere) '' ball c r) =
      ((↑) : ℂ → Sphere) '' sphere c r := by
  have h := frontier_sphere_image_jordanInterior (roundJordanAt c r hr)
  rw [roundJordanAt_interior,frontier_ball c hr.ne'] at h
  exact h

lemma IsConformalEquivalence.tendsto_disk_boundary_modulus {f : Sphere → Sphere}
    {U : Set Sphere} {c : ℂ} {r : ℝ}
    (hf : IsConformalEquivalence f U (((↑) : ℂ → Sphere) '' ball c r))
    (hr : 0<r) {p : Sphere} (hp : p∉U) :
    Tendsto (fun x => ‖finiteCoord (f x)-c‖) (𝓝[U] p) (𝓝 r) := by
  have hV : IsOpen (((↑) : ℂ → Sphere) '' ball c r) :=
    OnePoint.isOpen_image_coe.mpr isOpen_ball
  have ht := hf.tendsto_frontier hV hp
  have hc : ∀y∈frontier (((↑) : ℂ → Sphere) '' ball c r),
      ContinuousAt (fun x : Sphere => ‖finiteCoord x-c‖) y := by
    intro y hy
    rw [frontier_sphere_ball c hr] at hy
    obtain ⟨z,_,rfl⟩ := hy
    exact ((continuousAt_finiteCoord_of_ne_infty (OnePoint.coe_ne_infty z)).sub
      continuousAt_const).norm
  have he : ∀y∈frontier (((↑) : ℂ → Sphere) '' ball c r),‖finiteCoord y-c‖=r := by
    intro y hy
    rw [frontier_sphere_ball c hr] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa only [finiteCoord_coe,mem_sphere_iff_norm] using hz
  exact (tendsto_of_constant_on_set hc he).comp ht

end CircleDomainRigidity

end

end OAI
