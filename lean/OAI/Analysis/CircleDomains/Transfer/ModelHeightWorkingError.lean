import OAI.Analysis.CircleDomains.Transfer.ModelHeightSourceError
import OAI.Analysis.CircleDomains.Transfer.ModelWorkingCoordinates
import OAI.Analysis.CircleDomains.Sobolev.SummableEnergyCutoffs

namespace OAI

/-! Uniform and L2 errors for the actual compact descended height on a
source working region whose image is retained by the target cutoff. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem compact_height_uniform_error (M : CompactScalarModel G u)
    {R d ζ δ : ℝ} (H : ControlledHeight R d) (T : ℝ → ℝ)
    (hT : ∀ t, |T t-t| ≤ ζ) (η : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hH : |H.height (M.function (complexPlaneCoordinates x))-
      (M.function (complexPlaneCoordinates x)).im| ≤ δ) :
    |sphereFromPlaneFunction (fun y => η y*T (H.height (complexPlaneCoordinates y)))
      (invFun M.projection (planeSphere x))-(M.function (complexPlaneCoordinates x)).im| ≤ ζ+δ := by
  rw [M.scalar_section_on_domain _ hx]
  simp only [planeSphere, extendAtInfinity_coe, sphereFromPlaneFunction_coe, hη,
    complexPlaneCoordinates.apply_symm_apply, one_mul]
  exact (abs_sub_le _ _ _).trans (add_le_add (hT _) hH)

 theorem compact_height_source_error_L2 (M : CompactScalarModel G u)
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
        (fun y => η y*(T (H.height (complexPlaneCoordinates y))-y 1))) (physicalPlaneDomain G))
    {B : ℝ} (hE : (∫ x in physicalPlaneDomain G, E.weakGrad x 0^2+E.weakGrad x 1^2) ≤ B) :
    (eLpNorm (fun x => Q.weakGrad x-Y.weakGrad x) 2 (volume.restrict U)).toReal^2 ≤ B := by
  have hm := Q.weakGrad_memLp.sub Y.weakGrad_memLp
  have hn := integral_sq_eq_eLpNorm_toReal_sq hm.norm
  rw [eLpNorm_norm _ hm.aestronglyMeasurable] at hn
  change (eLpNorm (Q.weakGrad-Y.weakGrad) 2 (volume.restrict U)).toReal^2 ≤ B
  rw [← hn]
  exact (M.compact_height_source_error_energy H T η hU hUG hη Q Y E).trans hE

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
