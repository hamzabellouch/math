import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan
import OAI.Analysis.CircleDomains.Topology.DiskCrossingInput

namespace OAI

/-! Actual complex disk and measurable circle coordinates for a spherical
Jordan collar. -/

open Set Function Metric MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def sphereJordanCoordinate (K : ℂ ≃ₜ ℂ) (x : Sphere) : ℂ := K.symm (finiteCoord x)

def sphereJordanBoundary (K : ℂ ≃ₜ ℂ) (θ : UnitAddCircle) : Sphere :=
  ((K (standardCirclePoint θ) : ℂ) : Sphere)

theorem range_sphereJordanBoundary (K : ℂ ≃ₜ ℂ) :
    range (sphereJordanBoundary K) = frontier (((↑) : ℂ → Sphere) '' jordanInterior K) := by
  rw [frontier_sphere_image_jordanInterior, frontier_jordanInterior]
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨_, ⟨standardCirclePoint θ,
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero θ).property, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective ⟨z, hz⟩
    exact ⟨θ, congrArg (fun z : Circle => ((K (z : ℂ) : ℂ) : Sphere)) hθ⟩

theorem measurableEmbedding_sphereJordanBoundary (K : ℂ ≃ₜ ℂ) :
    MeasurableEmbedding (sphereJordanBoundary K) := by
  have hi : Topology.IsEmbedding (sphereJordanBoundary K) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp (K.isEmbedding.comp
      (Topology.IsEmbedding.subtypeVal.comp
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).isEmbedding))
  exact hi.measurableEmbedding (by rw [range_sphereJordanBoundary]; exact isClosed_frontier.measurableSet)

theorem sphereJordanCoordinate_continuousOn (K : ℂ ≃ₜ ℂ) :
    ContinuousOn (sphereJordanCoordinate K)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  exact K.symm.continuous.comp_continuousOn
    (continuousOn_finiteCoord_of_avoids_infty (by
      rw [closure_sphere_image_jordanInterior]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz))

theorem sphereJordanCoordinate_injOn (K : ℂ ≃ₜ ℂ) :
    InjOn (sphereJordanCoordinate K) (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) := by
  intro x hx y hy h
  rw [closure_sphere_image_jordanInterior] at hx hy
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  exact congrArg ((↑) : ℂ → Sphere) (K.symm.injective h)

theorem sphereJordanCoordinate_mapsTo (K : ℂ ≃ₜ ℂ) :
    MapsTo (sphereJordanCoordinate K)
      (closure (((↑) : ℂ → Sphere) '' jordanInterior K)) (closedBall 0 1) := by
  intro x hx
  rw [closure_sphere_image_jordanInterior, closure_jordanInterior] at hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
  simpa only [sphereJordanCoordinate, finiteCoord_coe, K.symm_apply_apply] using hz

theorem sphereJordanCoordinate_boundary_inverse (K : ℂ ≃ₜ ℂ) :
    ∀ x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K),
      sphereJordanCoordinate K x = standardCirclePoint
        ((measurableEmbedding_sphereJordanBoundary K).invFun x) := by
  intro x hx
  rw [← range_sphereJordanBoundary] at hx
  obtain ⟨θ, rfl⟩ := hx
  rw [(measurableEmbedding_sphereJordanBoundary K).leftInverse_invFun θ]
  simp only [sphereJordanCoordinate, sphereJordanBoundary, finiteCoord_coe, K.symm_apply_apply]

end CircleDomainRigidity

end

end OAI
