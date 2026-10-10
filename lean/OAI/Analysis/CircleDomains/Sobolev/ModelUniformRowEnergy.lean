import OAI.Analysis.CircleDomains.Sobolev.ModelWorkingGradients
import OAI.Analysis.CircleDomains.Uniformization.ModelUniformBounds

namespace OAI

/-! Uniform image bounds give a uniform energy budget for the reference
rows on the actual source working disk. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem horizontalSection_fderiv_norm_sq (M : CompactScalarModel G u)
    (hG : IsOpen G) {z : ℂ} (hz : (z : Sphere) ∈ G) :
    ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖^2 = ‖deriv M.function z‖^2 := by
  have hh : (fun w : ℂ => M.horizontalSection (w : Sphere)) =ᶠ[𝓝 z]
      (fun w => (M.function w).re) := by
    filter_upwards [(hG.preimage OnePoint.continuous_coe).mem_nhds hz] with w hw
    simpa only [extendAtInfinity_coe,finiteCoord_coe] using M.horizontalSection_on_domain hw
  rw [hh.fderiv_eq]
  exact holomorphic_real_fderiv_norm_sq (finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz))

 theorem working_row_energy_le (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, (z : Sphere) ∈ G → z ∈ ball 0 L → ‖M.function z‖ ≤ K)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (∫ x in physicalPlaneDomain G ∩ ball 0 L, ‖Wx.weakGrad x‖^2) ≤ Real.pi*K^2 := by
  let D := {z : ℂ | (z : Sphere) ∈ G} ∩ ball (0 : ℂ) L
  have hD : IsOpen D := (hG.preimage OnePoint.continuous_coe).inter isOpen_ball
  have he : complexPlaneCoordinates ⁻¹' D = physicalPlaneDomain G ∩ ball 0 L := by
    ext x
    simp only [D, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right,
      complexPlaneCoordinates_norm]
    rfl
  have hder := integral_norm_deriv_sq_eq_image_area hD.measurableSet
    (fun z hz => finite_differentiable_of_sphere_conformal (M.conformal.1 _ hz.1))
    (fun z hz w hw he => by
      apply OnePoint.coe_injective
      apply M.conformal.bijOn.injOn hz.1 hw.1
      simpa only [extendAtInfinity_coe] using congrArg ((↑) : ℂ → Sphere) he)
  have hsub : M.function '' D ⊆ closedBall 0 K := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz.1 hz.2
  have hvol : (volume (M.function '' D)).toReal ≤ Real.pi*K^2 := by
    have hv : (volume (M.function '' D)).toReal ≤ (volume (closedBall (0 : ℂ) K)).toReal :=
      ENNReal.toReal_mono measure_closedBall_lt_top.ne (measure_mono hsub)
    simpa only [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_ofReal hK, mul_comm] using hv
  calc
    _ = ∫ x in physicalPlaneDomain G ∩ ball 0 L,
        ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) (complexPlaneCoordinates x)‖^2 := by
      apply integral_congr_ae
      filter_upwards [M.working_horizontal_norm hG hinf L Wx] with x hx
      rw [hx]
    _ = ∫ z in D, ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖^2 := by
      rw [← he]
      exact complexPlaneCoordinates_measurePreserving.setIntegral_preimage_emb
        complexPlaneCoordinates.toHomeomorph.measurableEmbedding
          (fun z : ℂ => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖^2) D
    _ = ∫ z in D, ‖deriv M.function z‖^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hD.measurableSet] with z hz
      exact M.horizontalSection_fderiv_norm_sq hG hz.1
    _ = (volume (M.function '' D)).toReal := hder
    _ ≤ _ := hvol

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
