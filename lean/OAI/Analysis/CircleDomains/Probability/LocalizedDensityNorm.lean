import OAI.Analysis.CircleDomains.Probability.SphericalDensityNorm
import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates

namespace OAI

/-! Outside the permitted perturbation region, the smoothed barrier is
controlled by the original spherical density, with one fixed chart constant. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem spherical_weighted_density_eLpNorm_euclidean_le
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    eLpNorm (fun x : EuclideanPlane =>
      (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) 2 volume ≤
      (∫⁻y, g y ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  have hmp : MeasurePreserving complexPlaneCoordinates volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
      euclideanPlaneCoordinates_measurePreserving
  rw [show (fun x : EuclideanPlane =>
      (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) =
    (fun z : ℂ => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)) ∘
      complexPlaneCoordinates from rfl]
  rw [eLpNorm_comp_measurePreserving
    (global_spherical_weighted_density_memLp g hg he).aestronglyMeasurable hmp]
  exact global_spherical_weighted_density_eLpNorm_le g hg he

theorem localized_perturbed_density_eLpNorm_le
    {X : Type*} (π : Sphere → X) (O : Set X) (S : Set EuclideanPlane)
    (hS : MeasurableSet S) (hSO : ∀x ∈ S, π (planeSphere x) ∉ O)
    (g g₁ : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞)
    (hagree : ∀y, π y ∉ O → g₁ y = g y) (C : ℝ) (hC : 0 ≤ C) :
    eLpNorm (fun x : EuclideanPlane => C *
      ((g₁ (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)))
        2 (volume.restrict S) ≤
      ENNReal.ofReal C * (∫⁻y, g y ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) := by
  have heq : (fun x : EuclideanPlane => C *
      ((g₁ (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) =ᵐ[volume.restrict S]
      (fun x => C * ((g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) := by
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [hagree _ (hSO x hx)]
  rw [eLpNorm_congr_ae heq]
  calc
    _ ≤ eLpNorm (fun x : EuclideanPlane => C *
        ((g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = ENNReal.ofReal C * eLpNorm (fun x : EuclideanPlane =>
        (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) 2 volume := by
      rw [show (fun x : EuclideanPlane => C *
          ((g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2))) =
        C • (fun x : EuclideanPlane =>
          (g (planeSphere x)).toReal / (1 + ‖complexPlaneCoordinates x‖ ^ 2)) from rfl,
        eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC]
    _ ≤ _ := mul_le_mul' le_rfl (spherical_weighted_density_eLpNorm_euclidean_le g hg he)

end CircleDomainRigidity

end

end OAI
