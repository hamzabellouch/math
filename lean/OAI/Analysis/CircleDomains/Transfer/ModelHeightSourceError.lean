import OAI.Analysis.CircleDomains.Rigidity.ModelCompactHeightTrace
import OAI.Analysis.CircleDomains.Transfer.ModelHeightErrorTransport

namespace OAI

/-! Identification of the transported compact vertical error with the
actual source height error on a region retained by the target cutoff.
The energy comparison uses uniqueness of weak gradients. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_error_on_source (M : CompactScalarModel G u)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1) :
    planeInverseTransport (extendAtInfinity M.function)
      (fun y => η y*(T (H.height (complexPlaneCoordinates y))-y 1)) x =
    sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
      (invFun M.projection (planeSphere x))-(M.function (complexPlaneCoordinates x)).im := by
  rw [M.scalar_section_on_domain _ hx, planeInverseTransport_extendAtInfinity]
  simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe,
    complexPlaneCoordinates.apply_symm_apply, hη, one_mul]
  rfl

 theorem compact_height_source_error_energy (M : CompactScalarModel G u)
    {R d : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (hUG : U ⊆ physicalPlaneDomain G)
    (hη : ∀ x ∈ U, η (complexPlaneCoordinates.symm
      (M.function (complexPlaneCoordinates x))) = 1)
    (Q : DeGiorgi.MemW1pWitness 2 (fun x =>
      sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
        (invFun M.projection (planeSphere x))) U)
    (Y : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im) U)
    (E : DeGiorgi.MemW1pWitness 2
      (planeInverseTransport (extendAtInfinity M.function)
        (fun y => η y*(T (H.height (complexPlaneCoordinates y))-y 1))) (physicalPlaneDomain G)) :
    (∫ x in U, ‖Q.weakGrad x-Y.weakGrad x‖^2) ≤
      ∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2 := by
  let W := subtractSobolevWitness Q Y
  let E' := (E.restrict hU hUG).congr_ae
    ((ae_restrict_mem hU.measurableSet).mono (fun x hx =>
      M.compact_height_error_on_source H T η (hUG hx) (hη x hx)))
  have he := W.ae_eq hU E'
  have he' : ∀ᵐ x ∂volume.restrict U, Q.weakGrad x-Y.weakGrad x = E.weakGrad x := by
    filter_upwards [he] with x hx
    simpa only [W, subtractSobolevWitness_gradient, E',
      DeGiorgi.MemW1pWitness.congr_ae, DeGiorgi.MemW1pWitness.restrict] using hx
  have hi : Integrable (fun x => ‖E.weakGrad x‖^2) (volume.restrict (physicalPlaneDomain G)) :=
    E.weakGrad_norm_memLp.integrable_sq
  calc
    _ = ∫ x in U, ‖E.weakGrad x‖^2 := integral_congr_ae
      (he'.mono (fun _ hx => congrArg (fun z : EuclideanPlane => ‖z‖^2) hx))
    _ ≤ ∫ x in physicalPlaneDomain G, ‖E.weakGrad x‖^2 :=
      setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
        (Eventually.of_forall hUG)
    _ = _ := by simp only [plane_norm_sq]

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
