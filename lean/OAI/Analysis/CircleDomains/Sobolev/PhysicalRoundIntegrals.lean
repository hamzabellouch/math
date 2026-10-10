import OAI.Analysis.CircleDomains.Sobolev.SmoothDiskGreen
import OAI.Analysis.CircleDomains.Sobolev.ComplexSobolevTransport

namespace OAI

/-! Exact transport of round-disk integrals and smooth partial derivatives
between the physical Euclidean plane and the complex plane. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem complexPlaneCoordinates_norm (x : EuclideanPlane) :
    ‖complexPlaneCoordinates x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.real_norm_sq_eq]
  simp only [complexPlaneCoordinates_apply, Fin.sum_univ_two]
  ring

 theorem complexPlaneCoordinates_preimage_ball (R : ℝ) :
    complexPlaneCoordinates ⁻¹' ball (0 : ℂ) R = ball (0 : EuclideanPlane) R := by
  ext x
  simp only [mem_preimage, mem_ball, dist_zero_right, complexPlaneCoordinates_norm]

 theorem complexPlaneCoordinates_integral_ball (R : ℝ) (g : ℂ → ℝ) :
    (∫ x in ball (0 : EuclideanPlane) R, g (complexPlaneCoordinates x)) =
      ∫ z in ball (0 : ℂ) R, g z := by
  rw [← complexPlaneCoordinates_preimage_ball]
  exact complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding g _

 theorem physical_real_volume_ball (R : ℝ) (hR : 0 ≤ R) :
    (volume (ball (0 : EuclideanPlane) R)).toReal = Real.pi*R^2 := by
  have hh := complexPlaneCoordinates_integral_ball R (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ] at hh
  rw [hh, real_volume_ball 0 hR]

 theorem physical_complex_partial {a : EuclideanPlane → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x v : EuclideanPlane) :
    fderiv ℝ (fun z => a (complexPlaneCoordinates.symm z)) (complexPlaneCoordinates x)
      (complexPlaneCoordinates v) = fderiv ℝ a x v := by
  change fderiv ℝ (a ∘ complexPlaneCoordinates.symm) (complexPlaneCoordinates x)
    (complexPlaneCoordinates v) = _
  rw [fderiv_comp (complexPlaneCoordinates x) (ha.differentiable (by simp)).differentiableAt
      complexPlaneCoordinates.symm.differentiableAt, complexPlaneCoordinates.symm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

 theorem smooth_physical_disk_vertical_flux (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {a : EuclideanPlane → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    (∫ x in ball (0 : EuclideanPlane) R, fderiv ℝ a x (EuclideanSpace.single 1 1)) =
      planarFormIntegral (fun z => -a (complexPlaneCoordinates.symm z))
        (fun _ => 0) (unitCircleParam 0 R) := by
  calc
    _ = ∫ x in ball (0 : EuclideanPlane) R,
        fderiv ℝ (fun z => a (complexPlaneCoordinates.symm z))
          (complexPlaneCoordinates x) Complex.I := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [← complexPlaneCoordinates_one, physical_complex_partial ha]
    _ = ∫ z in ball (0 : ℂ) R, fderiv ℝ (fun w => a (complexPlaneCoordinates.symm w)) z Complex.I :=
      complexPlaneCoordinates_integral_ball R (fun z => fderiv ℝ (fun w => a (complexPlaneCoordinates.symm w)) z Complex.I)
    _ = _ := by
      simpa only [Function.comp_def] using smooth_disk_vertical_flux hgreen R hR (ha.comp complexPlaneCoordinates.symm.contDiff)

 theorem smooth_physical_disk_jacobian (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) {a b : EuclideanPlane → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    (∫ x in ball (0 : EuclideanPlane) R,
      fderiv ℝ a x (EuclideanSpace.single 0 1) * fderiv ℝ b x (EuclideanSpace.single 1 1) -
        fderiv ℝ a x (EuclideanSpace.single 1 1) * fderiv ℝ b x (EuclideanSpace.single 0 1)) =
      planarFormIntegral
        (fun z => a (complexPlaneCoordinates.symm z) *
          fderiv ℝ (fun w => b (complexPlaneCoordinates.symm w)) z 1)
        (fun z => a (complexPlaneCoordinates.symm z) *
          fderiv ℝ (fun w => b (complexPlaneCoordinates.symm w)) z Complex.I)
        (unitCircleParam 0 R) := by
  let A := fun z => a (complexPlaneCoordinates.symm z)
  let B := fun z => b (complexPlaneCoordinates.symm z)
  calc
    _ = ∫ x in ball (0 : EuclideanPlane) R,
        fderiv ℝ A (complexPlaneCoordinates x) 1 *
          fderiv ℝ B (complexPlaneCoordinates x) Complex.I -
        fderiv ℝ A (complexPlaneCoordinates x) Complex.I *
          fderiv ℝ B (complexPlaneCoordinates x) 1 := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [A, B]
      rw [← complexPlaneCoordinates_zero, ← complexPlaneCoordinates_one,
        physical_complex_partial ha, physical_complex_partial hb,
        physical_complex_partial ha, physical_complex_partial hb]
    _ = ∫ z in ball (0 : ℂ) R, fderiv ℝ A z 1 * fderiv ℝ B z Complex.I -
        fderiv ℝ A z Complex.I * fderiv ℝ B z 1 :=
      complexPlaneCoordinates_integral_ball R (fun z => fderiv ℝ A z 1 * fderiv ℝ B z Complex.I -
        fderiv ℝ A z Complex.I * fderiv ℝ B z 1)
    _ = _ := by
      simpa only [Function.comp_def] using smooth_disk_jacobian hgreen R hR
        (ha.comp complexPlaneCoordinates.symm.contDiff) (hb.comp complexPlaneCoordinates.symm.contDiff)

end CircleDomainRigidity

end

end OAI
