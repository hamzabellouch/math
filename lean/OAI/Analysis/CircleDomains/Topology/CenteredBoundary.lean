import OAI.Analysis.CircleDomains.Probability.DiskStartLaw

namespace OAI

/-! The positive angular parametrization and inverse of a centered Jordan boundary. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric

theorem standardCirclePoint_normalizedArgument {z : ℂ} (hz : ‖z‖ = 1) :
    standardCirclePoint (normalizedArgument z) = z := by
  change (Circle.exp (Complex.arg z * ((2 * Real.pi)⁻¹ * 1) *
    ((1 : ℝ)⁻¹ * (2 * Real.pi))) : ℂ) = z
  have he : Complex.arg z * ((2 * Real.pi)⁻¹ * 1) *
      ((1 : ℝ)⁻¹ * (2 * Real.pi)) = Complex.arg z := by
    field_simp
  rw [he]
  exact congrArg ((↑) : Circle → ℂ)
    (Circle.exp_arg ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩)

@[simp] theorem normalizedArgument_standardCirclePoint (θ : UnitAddCircle) :
    normalizedArgument (standardCirclePoint θ) = θ := by
  apply standardCirclePoint_injective
  exact standardCirclePoint_normalizedArgument (Circle.norm_coe _)

def centeredJordanBoundary (K : ℂ ≃ₜ ℂ) (b : Sphere) (θ : UnitAddCircle) : Sphere :=
  ((K (diskCentering (-sphereJordanCoordinate K b) (standardCirclePoint θ)) : ℂ) : Sphere)

theorem continuous_centeredJordanBoundary (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) :
    Continuous (centeredJordanBoundary K b) := by
  have ha : ‖-sphereJordanCoordinate K b‖ < 1 := by
    simpa only [norm_neg] using sphereJordanCoordinate_norm_lt K hb
  apply OnePoint.continuous_coe.comp
  apply K.continuous.comp
  apply (continuousOn_diskCentering ha).comp_continuous
    (continuous_subtype_val.comp (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous)
  intro θ
  exact mem_closedBall_zero_iff.mpr (Circle.norm_coe _).le

theorem centeredJordanBoundary_mem_frontier (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) (θ : UnitAddCircle) :
    centeredJordanBoundary K b θ ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K) := by
  rw [frontier_sphere_image_jordanInterior, frontier_jordanInterior]
  refine ⟨_, ⟨_, ?_, rfl⟩, rfl⟩
  apply mem_sphere_zero_iff_norm.mpr
  apply diskCentering_norm_eq_one
  · simpa only [norm_neg] using sphereJordanCoordinate_norm_lt K hb
  · exact Circle.norm_coe _

theorem centeredJordanCoordinate_boundary (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) (θ : UnitAddCircle) :
    centeredJordanCoordinate K b (centeredJordanBoundary K b θ) = standardCirclePoint θ := by
  change diskCentering (sphereJordanCoordinate K b)
    (K.symm (K (diskCentering (-sphereJordanCoordinate K b) (standardCirclePoint θ)))) = _
  rw [K.symm_apply_apply]
  have h := diskCentering_inverse
    (a := -sphereJordanCoordinate K b) (z := standardCirclePoint θ)
    (by simpa only [norm_neg] using sphereJordanCoordinate_norm_lt K hb)
    (Circle.norm_coe _).le
  simpa only [neg_neg] using h

theorem centeredJordanBoundary_inverse (K : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior K) {x : Sphere}
    (hx : x ∈ frontier (((↑) : ℂ → Sphere) '' jordanInterior K)) :
    centeredJordanBoundary K b (normalizedArgument (centeredJordanCoordinate K b x)) = x := by
  apply centeredJordanCoordinate_injOn K hb
    (frontier_subset_closure (centeredJordanBoundary_mem_frontier K hb _))
    (frontier_subset_closure hx)
  rw [centeredJordanCoordinate_boundary K hb,
    standardCirclePoint_normalizedArgument (centeredJordanCoordinate_norm_boundary K hb hx)]

end CircleDomainRigidity

end

end OAI
