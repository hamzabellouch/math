import OAI.Analysis.CircleDomains.Sobolev.HolomorphicWeakRows
import OAI.Analysis.CircleDomains.Transfer.ModelWorkingCoordinates

namespace OAI

/-! The reference rows on a source working disk are the actual model
coordinate gradients, with equal norms and the exact horizontal norm. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem working_rows_norm_eq (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (fun x => ‖Wx.weakGrad x‖) =ᵐ[volume.restrict (physicalPlaneDomain G ∩ ball 0 L)]
      fun x => ‖Wy.weakGrad x‖ := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have he : complexPlaneCoordinates ⁻¹' (D ∩ ball 0 L) = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [mem_preimage, mem_inter_iff, D, mem_ofPred_eq, mem_ball,
      dist_zero_right, complexPlaneCoordinates_norm]
    rfl
  obtain ⟨hEr,hEi⟩ := M.source_coordinate_memLp hG hinf L
  have hf : DifferentiableOn ℂ M.function (D ∩ ball 0 L) := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1)).differentiableWithinAt
  have h := holomorphic_weak_rows_norm_eq (hD.inter isOpen_ball) hf hEr hEi
  rw [he] at h
  exact h Wx Wy

 theorem working_horizontal_norm (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (fun x => ‖Wx.weakGrad x‖) =ᵐ[volume.restrict (physicalPlaneDomain G ∩ ball 0 L)]
      fun x => ‖fderiv ℝ (fun z : ℂ => M.horizontalSection (z : Sphere)) (complexPlaneCoordinates x)‖ := by
  let D := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have he : complexPlaneCoordinates ⁻¹' (D ∩ ball 0 L) = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [mem_preimage, mem_inter_iff, D, mem_ofPred_eq, mem_ball,
      dist_zero_right, complexPlaneCoordinates_norm]
    rfl
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz)).differentiableWithinAt
  have hs : ContDiffOn ℝ ∞ (fun z => (M.function z).re) (D ∩ ball 0 L) := (Complex.reCLM.contDiff.comp_contDiffOn ((hf.contDiffOn hD).restrict_scalars ℝ)).mono
    (inter_subset_left : D ∩ ball 0 L ⊆ D)
  have hn := complex_weak_gradient_norm (hD.inter isOpen_ball) hs
    (M.source_coordinate_memLp hG hinf L).1
  rw [he] at hn
  filter_upwards [hn Wx, ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hx hxU
  rw [hx]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hD.mem_nhds hxU.1] with z hz
  exact (show M.horizontalSection (z : Sphere) = (M.function z).re from by
    simpa only [planeSphere, extendAtInfinity_coe, finiteCoord_coe] using M.horizontalSection_on_domain hz).symm

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
