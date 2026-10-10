import OAI.Analysis.CircleDomains.Sobolev.QuarterTurnEnergy

namespace OAI

/-! Swapping the two Cartesian axes preserves Dirichlet energy and round disks. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

def axisSwap : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans quarterTurn

@[simp] theorem axisSwap_apply (z : ℂ) : axisSwap z = Complex.I * conj z := rfl

@[simp] theorem axisSwap_one : axisSwap 1 = Complex.I := by simp

@[simp] theorem axisSwap_I : axisSwap Complex.I = 1 := by simp

@[simp] theorem axisSwap_re (z : ℂ) : (axisSwap z).re = z.im := by simp

@[simp] theorem axisSwap_im (z : ℂ) : (axisSwap z).im = z.re := by simp

@[simp] theorem axisSwap_axisSwap (z : ℂ) : axisSwap (axisSwap z) = z := by
  apply Complex.ext <;> simp

@[simp] theorem axisSwap_symm_apply (z : ℂ) : axisSwap.symm z = axisSwap z := by
  apply axisSwap.injective
  rw [axisSwap.apply_symm_apply, axisSwap_axisSwap]

theorem axisSwap_preimage_closedBall (z : ℂ) (r : ℝ) :
    axisSwap ⁻¹' closedBall z r = closedBall (axisSwap z) r := by
  have h := axisSwap.toIsometryEquiv.preimage_closedBall z r
  change axisSwap ⁻¹' closedBall z r = closedBall (axisSwap.symm z) r at h
  simpa only [axisSwap_symm_apply] using h

theorem euclideanGradientEnergy_axisSwap {v : ℂ → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (axisSwap z)) :
    euclideanGradientEnergy (v ∘ axisSwap) z = euclideanGradientEnergy v (axisSwap z) := by
  have hd := (hv.hasFDerivAt.comp z axisSwap.hasFDerivAt).fderiv
  unfold euclideanGradientEnergy
  rw [hd]
  change (fderiv ℝ v (axisSwap z) (axisSwap 1)) ^ 2 +
    (fderiv ℝ v (axisSwap z) (axisSwap Complex.I)) ^ 2 = _
  rw [axisSwap_one, axisSwap_I]
  exact add_comm _ _

theorem integral_energy_axisSwap
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v U)
    (hi : IntegrableOn (euclideanGradientEnergy v) U) :
    IntegrableOn (euclideanGradientEnergy (v ∘ axisSwap)) (axisSwap ⁻¹' U) ∧
      (∫ z in axisSwap ⁻¹' U, euclideanGradientEnergy (v ∘ axisSwap) z) =
        ∫ z in U, euclideanGradientEnergy v z := by
  have hm := axisSwap.measurePreserving.restrict_preimage_emb
    axisSwap.toMeasurableEquiv.measurableEmbedding U
  have hc : IntegrableOn (euclideanGradientEnergy v ∘ axisSwap) (axisSwap ⁻¹' U) :=
    (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : euclideanGradientEnergy (v ∘ axisSwap) =ᵐ[volume.restrict (axisSwap ⁻¹' U)]
      euclideanGradientEnergy v ∘ axisSwap := by
    filter_upwards [ae_restrict_mem (hU.preimage axisSwap.continuous).measurableSet] with z hz
    exact euclideanGradientEnergy_axisSwap
      ((hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  refine ⟨hc.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact axisSwap.measurePreserving.setIntegral_preimage_emb
    axisSwap.toMeasurableEquiv.measurableEmbedding (euclideanGradientEnergy v) U

end CircleDomainRigidity

end

end OAI
