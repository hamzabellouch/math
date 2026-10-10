import OAI.Analysis.CircleDomains.Sobolev.ComplexScalarEnergy
import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness

namespace OAI

/-! A compact continuous complex-plane scalar with square-integrable
classical differential on an open set has its actual physical Sobolev
witness. This is used for the compact horizontal priority test. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_source_sobolev_witness
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hc : Continuous f) (hs : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ f D)
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D)) :
    Nonempty (DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D)) := by
  let Ω := complexPlaneCoordinates ⁻¹' D
  let F := f ∘ complexPlaneCoordinates
  have hΩ : IsOpen Ω := hD.preimage complexPlaneCoordinates.continuous
  have hF : ContDiffOn ℝ ∞ F Ω :=
    hf.comp complexPlaneCoordinates.contDiff.contDiffOn (fun _ hp => hp)
  have hmajor : MemLp (fun p => ‖fderiv ℝ f (complexPlaneCoordinates p)‖) 2 (volume.restrict Ω) :=
    hE.norm.comp_measurePreserving (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet)
  have hpartial (i : Fin 2) : MemLp
      (fun p => fderiv ℝ F p (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
    have hm : AEStronglyMeasurable (fun p => fderiv ℝ F p (EuclideanSpace.single i 1))
        (volume.restrict Ω) :=
      ((hF.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const).aestronglyMeasurable hΩ.measurableSet
    apply hmajor.of_le hm
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with p hp
    have hd : DifferentiableAt ℝ f (complexPlaneCoordinates p) :=
      (hf.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
    change ‖fderiv ℝ (f ∘ complexPlaneCoordinates) p (EuclideanSpace.single i 1)‖ ≤ _
    rw [fderiv_comp p hd complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]
    have haxis : ‖complexPlaneCoordinates (EuclideanSpace.single i 1)‖ = 1 := by
      fin_cases i
      · change ‖complexPlaneCoordinates (EuclideanSpace.single (0 : Fin 2) 1)‖ = 1
        rw [complexPlaneCoordinates_zero, norm_one]
      · change ‖complexPlaneCoordinates (EuclideanSpace.single (1 : Fin 2) 1)‖ = 1
        rw [complexPlaneCoordinates_one, Complex.norm_I]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, haxis, mul_one,
      Real.norm_eq_abs, abs_norm] using
      (fderiv ℝ f (complexPlaneCoordinates p)).le_opNorm (complexPlaneCoordinates (EuclideanSpace.single i 1))
  refine ⟨{
    memLp := ((hc.comp complexPlaneCoordinates.continuous).memLp_of_hasCompactSupport
      (hs.comp_homeomorph complexPlaneCoordinates.toHomeomorph)).restrict Ω
    weakGrad := fun p => WithLp.toLp 2 (fun i => fderiv ℝ F p (EuclideanSpace.single i 1))
    weakGrad_component_memLp := hpartial
    isWeakGrad := fun i => weakPartial_of_smooth_on hΩ (hF.of_le (by simp)) i }⟩

end CircleDomainRigidity

end

end OAI
