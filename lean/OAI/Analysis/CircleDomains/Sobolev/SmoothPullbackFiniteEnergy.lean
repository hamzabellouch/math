import OAI.Analysis.CircleDomains.Sobolev.SmoothPlaneEnergyTransport
import OAI.Analysis.CircleDomains.Sobolev.PlaneCovectorEnergy
import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskSobolev
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! The actual smooth target scalar has finite pullback differential.
This is derived from conformal energy transport, not assumed for the mask. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer MatchedConformalEnds
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem smooth_pullback_finite_energy
    {f fi : Sphere → Sphere} {G H : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi G H) (hG : IsOpen G) (hH : IsOpen H)
    (hinf : OnePoint.infty ∈ G) (hfix : f OnePoint.infty = OnePoint.infty)
    (hfic : IsConformalOn fi H) {Φ : EuclideanPlane → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : HasCompactSupport Φ) :
    ContDiffOn ℝ 1 (Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f) (realPlaneDomain G) ∧
      MemLp (fderiv ℝ (Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f)) 2
        (volume.restrict (realPlaneDomain G)) := by
  have hparts (i : Fin 2) : MemLp (fun x => fderiv ℝ Φ x (EuclideanSpace.single i 1)) 2 volume :=
    ((hΦ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hΦs.fderiv_apply (𝕜 := ℝ) _)
  obtain ⟨hw,hD,_⟩ := smooth_plane_energy_transport heq.symm hH hG
    (heq.infty_mem_target hinf hfix) (heq.inverse_fixes_infty hinf hfix) hfic
    hΦ.contDiffOn (fun i => (hparts i).restrict _)
  let w := planeInverseTransport f Φ
  let b := Φ ∘ euclideanPlaneCoordinates.symm ∘ sphereRealMap f
  have he : b = w ∘ euclideanPlaneCoordinates.symm := by
    funext p
    simp only [b,w,planeInverseTransport,comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  have hbin : MapsTo euclideanPlaneCoordinates.symm (realPlaneDomain G) (physicalPlaneDomain G) := by
    intro p hp
    change euclideanPlaneCoordinates.symm p ∈ euclideanPlaneCoordinates ⁻¹' realPlaneDomain G
    simpa only [mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hp
  have hbc : ContDiffOn ℝ 1 b (realPlaneDomain G) := by
    rw [he]
    exact hw.comp euclideanPlaneCoordinates.symm.contDiff.contDiffOn hbin
  refine ⟨hbc,?_⟩
  have hw2 : MemLp (fderiv ℝ w) 2 (volume.restrict (physicalPlaneDomain G)) := by
    apply ((hD 0).norm.add (hD 1).norm).of_le
      ((measurable_fderiv ℝ w).aestronglyMeasurable)
    filter_upwards [] with x
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact planeCovector_norm_le _
  have hmp : MeasurePreserving euclideanPlaneCoordinates.symm (volume.restrict (realPlaneDomain G))
      (volume.restrict (physicalPlaneDomain G)) := by
    convert euclideanPlaneCoordinates_symm_measurePreserving.restrict_preimage
      (isOpen_physicalPlaneDomain hG).measurableSet using 1
    congr 1
  have hmaj := (hw2.norm.comp_measurePreserving hmp).mul_const ‖euclideanPlaneCoordinates.symm.toContinuousLinearMap‖
  apply hmaj.of_le (measurable_fderiv ℝ b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (realPlaneDomain_open hG).measurableSet] with p hp
  simp only [comp_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),he,
    fderiv_comp p ((hw.contDiffAt ((isOpen_physicalPlaneDomain hG).mem_nhds (hbin hp))).differentiableAt (by simp))
      euclideanPlaneCoordinates.symm.differentiableAt,euclideanPlaneCoordinates.symm.fderiv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

end CircleDomainRigidity

end

end OAI
