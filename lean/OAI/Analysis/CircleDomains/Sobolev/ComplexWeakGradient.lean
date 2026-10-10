import OAI.Analysis.CircleDomains.Sobolev.ComplexLocalScalarWitness
import OAI.Analysis.CircleDomains.Sobolev.SmoothWeakGradient
import OAI.Analysis.CircleDomains.Sobolev.CutoffEnergyAlgebra

namespace OAI

/-! The complex chart preserves covector norms, including differences,
and identifies the gradients used by the physical Sobolev witnesses. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complex_plane_covector_norm (L : ℂ →L[ℝ] ℝ) :
    ‖planeCovectorGradient (L.comp complexPlaneCoordinates.toContinuousLinearMap)‖ = ‖L‖ := by
  have he : ‖planeCovectorGradient (L.comp complexPlaneCoordinates.toContinuousLinearMap)‖^2 = ‖L‖^2 := by
    rw [plane_norm_sq, complexCovector_norm_sq]
    simp only [planeCovectorGradient, planePair_zero, planePair_one,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      complexPlaneCoordinates_zero, complexPlaneCoordinates_one]
  nlinarith [norm_nonneg (planeCovectorGradient (L.comp complexPlaneCoordinates.toContinuousLinearMap)),
    norm_nonneg L]

 theorem complexLocalScalarWitness_gradient
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hL : MemLp f 2 (volume.restrict D))
    (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D)) (x : EuclideanPlane) :
    (complexLocalScalarWitness hD hf hL hE).weakGrad x =
      planeCovectorGradient (fderiv ℝ (f ∘ complexPlaneCoordinates) x) := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [complexLocalScalarWitness, planeCovectorGradient]

 theorem complex_weak_gradient_ae
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hE : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (W : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates)
      (complexPlaneCoordinates ⁻¹' D)) :
    W.weakGrad =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)] fun x =>
      planeCovectorGradient ((fderiv ℝ f (complexPlaneCoordinates x)).comp
        complexPlaneCoordinates.toContinuousLinearMap) := by
  have hL : MemLp f 2 (volume.restrict D) := by
    have hmp := complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet
    have hb := W.memLp.comp_measurePreserving
      (hmp.symm complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)
    change MemLp (fun z => f (complexPlaneCoordinates (complexPlaneCoordinates.symm z))) 2
      (volume.restrict D) at hb
    simpa only [complexPlaneCoordinates.apply_symm_apply] using hb
  let V := complexLocalScalarWitness hD hf hL hE
  have he := W.ae_eq (hD.preimage complexPlaneCoordinates.continuous) V
  filter_upwards [he, ae_restrict_mem (hD.preimage complexPlaneCoordinates.continuous).measurableSet] with x hx hxD
  rw [hx, complexLocalScalarWitness_gradient]
  congr 1
  rw [fderiv_comp x ((hf.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by simp))
    complexPlaneCoordinates.differentiableAt, complexPlaneCoordinates.fderiv]

 theorem complex_weak_gradient_difference_norm
    {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hg : ContDiffOn ℝ ∞ g D)
    (hEf : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (hEg : MemLp (fderiv ℝ g) 2 (volume.restrict D))
    (Wf : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D))
    (Wg : DeGiorgi.MemW1pWitness 2 (g ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D)) :
    (fun x => ‖Wf.weakGrad x-Wg.weakGrad x‖) =ᵐ[volume.restrict (complexPlaneCoordinates ⁻¹' D)]
      fun x => ‖fderiv ℝ f (complexPlaneCoordinates x)-fderiv ℝ g (complexPlaneCoordinates x)‖ := by
  filter_upwards [complex_weak_gradient_ae hD hf hEf Wf,
    complex_weak_gradient_ae hD hg hEg Wg] with x hfx hgx
  rw [hfx, hgx, ← planeCovectorGradient_sub, ← ContinuousLinearMap.sub_comp,
    complex_plane_covector_norm]

 theorem complex_weak_gradient_difference_L2
    {D : Set ℂ} (hD : IsOpen D) {f g : ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f D) (hg : ContDiffOn ℝ ∞ g D)
    (hEf : MemLp (fderiv ℝ f) 2 (volume.restrict D))
    (hEg : MemLp (fderiv ℝ g) 2 (volume.restrict D))
    (Wf : DeGiorgi.MemW1pWitness 2 (f ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D))
    (Wg : DeGiorgi.MemW1pWitness 2 (g ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' D)) :
    eLpNorm (fun x => Wf.weakGrad x-Wg.weakGrad x) 2
      (volume.restrict (complexPlaneCoordinates ⁻¹' D)) =
    eLpNorm (fun z => fderiv ℝ f z-fderiv ℝ g z) 2 (volume.restrict D) := by
  have hW := Wf.weakGrad_memLp.aestronglyMeasurable.sub Wg.weakGrad_memLp.aestronglyMeasurable
  have hE := hEf.aestronglyMeasurable.sub hEg.aestronglyMeasurable
  calc
    _ = eLpNorm (fun x => ‖Wf.weakGrad x-Wg.weakGrad x‖) 2
        (volume.restrict (complexPlaneCoordinates ⁻¹' D)) := (eLpNorm_norm _ hW).symm
    _ = eLpNorm (fun x => ‖fderiv ℝ f (complexPlaneCoordinates x)-fderiv ℝ g (complexPlaneCoordinates x)‖) 2
        (volume.restrict (complexPlaneCoordinates ⁻¹' D)) :=
      eLpNorm_congr_ae (complex_weak_gradient_difference_norm hD hf hg hEf hEg Wf Wg)
    _ = eLpNorm (fun z => ‖fderiv ℝ f z-fderiv ℝ g z‖) 2 (volume.restrict D) :=
      eLpNorm_comp_measurePreserving hE.norm
        (complexPlaneCoordinates_measurePreserving.restrict_preimage hD.measurableSet)
    _ = _ := eLpNorm_norm _ hE

end CircleDomainRigidity

end

end OAI
