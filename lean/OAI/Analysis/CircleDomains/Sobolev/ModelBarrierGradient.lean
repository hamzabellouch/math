import OAI.Analysis.CircleDomains.Sobolev.ModelSmoothBarrier
import OAI.Analysis.CircleDomains.Sobolev.ComplexPhysicalGradient
import OAI.Analysis.CircleDomains.Transfer.ModelWorkingCoordinates

namespace OAI

/-! The reference differential in the selected barrier comparison is
exactly the weak gradient of the actual conformal pullback barrier. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem reference_barrier_value (M : CompactScalarModel G u)
    (Φ : EuclideanPlane → ℝ) (x : EuclideanPlane) :
    planeInverseTransport (extendAtInfinity M.function) Φ x =
      Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
        ((M.function (complexPlaneCoordinates x)).im)) := by
  rw [planeInverseTransport_extendAtInfinity]
  simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe]
  congr 1
  apply complexPlaneCoordinates.injective
  rw [complexPlaneCoordinates.apply_symm_apply]
  simp only [complexPlaneCoordinates_apply, planePair_zero, planePair_one]

 theorem reference_barrier_gradient (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L))
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (V : DeGiorgi.MemW1pWitness 2 (planeInverseTransport (extendAtInfinity M.function) Φ)
      (physicalPlaneDomain G))
    (hV : ∀ x, V.weakGrad x = planeCovectorGradient
      (fderiv ℝ (planeInverseTransport (extendAtInfinity M.function) Φ) x)) :
    V.weakGrad =ᵐ[volume.restrict (physicalPlaneDomain G ∩ ball 0 L)] fun x =>
      planeCovectorGradient ((fderiv ℝ Φ (planePair ((M.function (complexPlaneCoordinates x)).re)
        ((M.function (complexPlaneCoordinates x)).im))).comp
          (weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x))) := by
  let D := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L
  have hD : IsOpen D := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  have he : complexPlaneCoordinates ⁻¹' D = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [D, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right,
      complexPlaneCoordinates_norm]
    rfl
  have hf : DifferentiableOn ℂ M.function D := fun z hz =>
    (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1)).differentiableWithinAt
  have hs : ContDiffOn ℝ ∞ M.function D := (hf.contDiffOn hD).restrict_scalars ℝ
  have hx := complex_weak_physical_gradient_ae hD
    (Complex.reCLM.contDiff.comp_contDiffOn hs) (M.source_coordinate_memLp hG hinf L).1
  have hy := complex_weak_physical_gradient_ae hD
    (Complex.imCLM.contDiff.comp_contDiffOn hs) (M.source_coordinate_memLp hG hinf L).2
  rw [he] at hx hy
  filter_upwards [hx Wx,hy Wy,
    ae_restrict_mem ((isOpen_physicalPlaneDomain hG).inter isOpen_ball).measurableSet] with x hxr hxi hxD
  rw [hV x, hxr, hxi, weakPairDifferential_covectors]
  congr 1
  have hf' : DifferentiableAt ℝ (fun x => M.function (complexPlaneCoordinates x)) x :=
    ((hs.contDiffAt (hD.mem_nhds (show complexPlaneCoordinates x ∈ D from by
      change x ∈ complexPlaneCoordinates ⁻¹' D
      rw [he]
      exact hxD))).differentiableAt (by simp)).comp x
        complexPlaneCoordinates.differentiableAt
  have hr := Complex.reCLM.differentiableAt.comp x hf'
  have hi := Complex.imCLM.differentiableAt.comp x hf'
  have hc := (hΦ.differentiable (by simp) _).hasFDerivAt.comp x
    (hasFDerivAt_planePair hr.hasFDerivAt hi.hasFDerivAt)
  rw [funext (M.reference_barrier_value Φ)]
  exact hc.fderiv

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
