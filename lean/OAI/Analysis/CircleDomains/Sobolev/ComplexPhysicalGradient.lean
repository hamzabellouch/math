import OAI.Analysis.CircleDomains.Sobolev.ComplexWeakGradient

namespace OAI

/-! The complex-chart gradient identification in terms of the physical
classical differential of the represented scalar. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_weak_physical_gradient_ae
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (W : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D)) :
    W.weakGrad =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)] fun x =>
      planeCovectorGradient (fderiv ℝ (f ∘ complexPlaneCoordinates) x) := by
  filter_upwards [complex_weak_gradient_ae hD hf hE W,
    ae_restrict_mem (hD.preimage complexPlaneCoordinates.continuous).measurableSet] with x hx hxD
  rw [hx]
  congr 1
  rw [fderiv_comp x ((hf.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by simp))
    complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]

 theorem weakPairDifferential_covectors (a b : EuclideanPlane →L[ℝ] ℝ) :
    weakPairDifferential (planeCovectorGradient a) (planeCovectorGradient b) =
      a.smulRight (EuclideanSpace.single (0 : Fin 2) 1)+
      b.smulRight (EuclideanSpace.single (1 : Fin 2) 1) := by
  unfold weakPairDifferential planeCovectorGradient
  rw [← plane_covector_of_basis a, ← plane_covector_of_basis b]

end CircleDomainRigidity

end

end OAI
