import OAI.Analysis.CircleDomains.Topology.CompactScalarModelFromCircle
import OAI.Analysis.CircleDomains.Sobolev.ConformalSobolevEnergyIdentity
import OAI.Analysis.CircleDomains.Transfer.ModelScalarPullback
import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra

namespace OAI

/-! The globally continued scalar has exactly its original source
Dirichlet energy. Apply conformal energy transport to the global target
scalar in the reverse direction and identify the source weak gradient. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarCircleModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem scalar_energy_eq (M : CompactScalarCircleModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)) (i : Fin m) :
    (∫ x, ‖(M.witness i).weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain G, ‖(W i).weakGrad x‖^2 := by
  let A := fun x => sphereFromPlaneFunction (u i) (M.projection (planeSphere x))
  have huc : Continuous (sphereFromPlaneFunction (u i)) := continuousOn_univ.mp
    (sphereFromPlaneFunction_continuousOn isOpen_univ (hu i).continuousOn
      (hs i).isCompact (fun x hx => image_eq_zero_of_notMem_tsupport hx))
  have hA : Continuous A := (huc.comp M.projection_continuous).comp continuous_planeSphere
  have hsA : HasCompactSupport A := M.scalar_compact hinf hs i
  obtain ⟨hfc,hmap,fi,hfic,hfimap,hl,hr⟩ := M.conformal
  have heq : IsSmoothSphereEquivalence fi (extendAtInfinity M.function)
      (extendAtInfinity M.function '' G) G :=
    ⟨fun p hp => hfic.isSmoothSphereAt M.circle.1 hp,hfimap,
      fun p hp => hfc.isSmoothSphereAt hG hp,hmap,hr,hl⟩
  have hfix : fi OnePoint.infty = OnePoint.infty := by
    simpa only [extendAtInfinity_infty] using hl _ hinf
  have hpull : EqOn (u i) (planeInverseTransport (extendAtInfinity M.function) A)
      (physicalPlaneDomain G) := by
    intro x hx
    rw [planeInverseTransport_extendAtInfinity]
    simp only [planeSphere,extendAtInfinity_coe,sphereFromPlaneFunction_coe]
    change u i x = sphereFromPlaneFunction (u i)
      (M.projection (planeSphere (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x)))))
    have he : planeSphere (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) =
        extendAtInfinity M.function (planeSphere x) := by
      simp only [planeSphere,complexPlaneCoordinates.apply_symm_apply,extendAtInfinity_coe]
    rw [he,M.projection_inverse _ hx]
    simp only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]
  obtain ⟨K,hK⟩ := sobolev_conformal_energy_identity heq M.circle.1 hG
    ⟨_,hinf,rfl⟩ hfix hfic hA hsA (M.witness i) hpull (W i).memLp
  have hsource : (∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2) =
      ∫ x in physicalPlaneDomain G, ‖(W i).weakGrad x‖^2 := by
    apply integral_congr_ae
    exact (K.ae_eq (isOpen_physicalPlaneDomain hG) (W i)).mono
      (fun _ he => congrArg (fun v : EuclideanPlane => ‖v‖^2) he)
  have hzero : ∀ᵐ x ∂volume, x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) →
      ‖(M.witness i).weakGrad x‖^2 = 0 := by
    filter_upwards [M.gradient_zero i 0,M.gradient_zero i 1] with x h0 h1 hx
    rw [plane_norm_sq,h0 hx,h1 hx]
    norm_num
  calc
    _ = ∫ x in physicalPlaneDomain (extendAtInfinity M.function '' G),
        ‖(M.witness i).weakGrad x‖^2 := (setIntegral_eq_integral_of_ae_compl_eq_zero hzero).symm
    _ = ∫ x in physicalPlaneDomain G, ‖K.weakGrad x‖^2 := by
      simpa only [plane_norm_sq] using hK.symm
    _ = _ := hsource

end CompactScalarCircleModel
end CircleDomainRigidity

end

end OAI
