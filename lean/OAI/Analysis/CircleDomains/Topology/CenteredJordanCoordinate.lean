import OAI.Analysis.CircleDomains.Topology.DiskCenteringHomeomorph
import OAI.Analysis.CircleDomains.Topology.SphereJordanCoordinates
import Mathlib.Topology.TietzeExtension

namespace OAI

/-! Centered disk coordinates for the actual spherical Jordan collars.
The continuous extension is used only to push path laws to path space. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

def centeredJordanCoordinate (K : ℂ ≃ₜ ℂ) (b x : Sphere) : ℂ :=
  diskCentering (sphereJordanCoordinate K b) (sphereJordanCoordinate K x)

theorem sphereJordanCoordinate_norm_lt (K : ℂ ≃ₜ ℂ) {x : Sphere}
    (hx : x ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ‖sphereJordanCoordinate K x‖ < 1 := by
  obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hx
  simpa only [sphereJordanCoordinate, finiteCoord_coe, K.symm_apply_apply,
    mem_ball_zero_iff] using hw

theorem sphereJordanCoordinate_norm_boundary (K : ℂ ≃ₜ ℂ) {x : Sphere}
    (hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    ‖sphereJordanCoordinate K x‖ = 1 := by
  rw [← range_sphereJordanBoundary] at hx
  obtain ⟨θ, rfl⟩ := hx
  change ‖K.symm (K (standardCirclePoint θ))‖ = 1
  rw [K.symm_apply_apply]
  exact Circle.norm_coe _

theorem centeredJordanCoordinate_continuousOn (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ContinuousOn (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) :=
  (continuousOn_diskCentering (sphereJordanCoordinate_norm_lt K hb)).comp
    (sphereJordanCoordinate_continuousOn K) (sphereJordanCoordinate_mapsTo K)

theorem centeredJordanCoordinate_injOn (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    InjOn (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  intro x hx y hy he
  apply sphereJordanCoordinate_injOn K hx hy
  exact diskCentering_injOn _ (sphereJordanCoordinate_norm_lt K hb)
    (sphereJordanCoordinate_mapsTo K hx) (sphereJordanCoordinate_mapsTo K hy) he

@[simp] theorem centeredJordanCoordinate_self (K : ℂ ≃ₜ ℂ) (b : Sphere) :
    centeredJordanCoordinate K b b = 0 := diskCentering_self _

theorem centeredJordanCoordinate_norm_le (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) {x : Sphere}
    (hx : x ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    ‖centeredJordanCoordinate K b x‖ ≤ 1 :=
  diskCentering_norm_le (sphereJordanCoordinate_norm_lt K hb)
    (mem_closedBall_zero_iff.mp (sphereJordanCoordinate_mapsTo K hx))

theorem centeredJordanCoordinate_norm_boundary (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) {x : Sphere}
    (hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    ‖centeredJordanCoordinate K b x‖ = 1 :=
  diskCentering_norm_eq_one (sphereJordanCoordinate_norm_lt K hb)
    (sphereJordanCoordinate_norm_boundary K hx)

theorem exists_centeredJordanExtension (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    ∃ F : C(Sphere, ℂ), EqOn F (centeredJordanCoordinate K b)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  let : TietzeExtension ℂ := TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  let S := closure (((↑) : ℂ → Sphere) '' jordanInterior K)
  let f : C(S, ℂ) := ⟨fun x => centeredJordanCoordinate K b x.val,
    continuousOn_iff_continuous_domRestrict.mp (centeredJordanCoordinate_continuousOn K hb)⟩
  obtain ⟨F, hF⟩ := f.exists_restrict_eq isClosed_closure
  refine ⟨F, fun x hx => ?_⟩
  exact congrArg (fun g : C(S, ℂ) => g ⟨x, hx⟩) hF

end CircleDomainRigidity

end

end OAI
