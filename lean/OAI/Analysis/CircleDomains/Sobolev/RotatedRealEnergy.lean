import OAI.Analysis.CircleDomains.Sobolev.QuarterTurnEnergy

namespace OAI

/-! Arbitrary planar rotation preserves the real gradient energy used in local crossing estimates. -/

open Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

private theorem real_linear_complex_expansion (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

theorem euclideanGradientEnergy_rotation (a : Circle) {v : ℂ → ℝ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (rotation a z)) :
    euclideanGradientEnergy (v ∘ rotation a) z = euclideanGradientEnergy v (rotation a z) := by
  have hd := (hv.hasFDerivAt.comp z (rotation a).hasFDerivAt).fderiv
  unfold euclideanGradientEnergy
  rw [hd]
  change (fderiv ℝ v (rotation a z) (rotation a 1)) ^ 2 +
    (fderiv ℝ v (rotation a z) (rotation a Complex.I)) ^ 2 = _
  rw [real_linear_complex_expansion _ (rotation a 1),
    real_linear_complex_expansion _ (rotation a Complex.I)]
  simp only [rotation_apply, mul_one, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero]
  have ha : (a : ℂ).re ^ 2 + (a : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, Circle.normSq_coe, pow_two] using
      (Complex.normSq_apply (a : ℂ)).symm.trans (Circle.normSq_coe a)
  linear_combination ((fderiv ℝ v ((a : ℂ) * z) 1) ^ 2 +
    (fderiv ℝ v ((a : ℂ) * z) Complex.I) ^ 2) * ha

theorem integral_energy_rotation_on (a : Circle)
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v U)
    {s : Set ℂ} (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hi : IntegrableOn (euclideanGradientEnergy v) s) :
    IntegrableOn (euclideanGradientEnergy (v ∘ rotation a)) (rotation a ⁻¹' s) ∧
      (∫ z in rotation a ⁻¹' s, euclideanGradientEnergy (v ∘ rotation a) z) =
        ∫ z in s, euclideanGradientEnergy v z := by
  have hm := (rotation a).measurePreserving.restrict_preimage_emb
    (rotation a).toMeasurableEquiv.measurableEmbedding s
  have hc : IntegrableOn (euclideanGradientEnergy v ∘ rotation a) (rotation a ⁻¹' s) :=
    (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : euclideanGradientEnergy (v ∘ rotation a) =ᵐ[volume.restrict (rotation a ⁻¹' s)]
      euclideanGradientEnergy v ∘ rotation a := by
    filter_upwards [ae_restrict_mem (hs.preimage (rotation a).continuous.measurable)] with z hz
    exact euclideanGradientEnergy_rotation a
      ((hv.contDiffAt (hU.mem_nhds (hsU hz))).differentiableAt (by norm_num))
  refine ⟨hc.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact (rotation a).measurePreserving.setIntegral_preimage_emb
    (rotation a).toMeasurableEquiv.measurableEmbedding (euclideanGradientEnergy v) s

theorem integral_energy_rotation (a : Circle)
    {U : Set ℂ} (hU : IsOpen U) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v U)
    (hi : IntegrableOn (euclideanGradientEnergy v) U) :
    IntegrableOn (euclideanGradientEnergy (v ∘ rotation a)) (rotation a ⁻¹' U) ∧
      (∫ z in rotation a ⁻¹' U, euclideanGradientEnergy (v ∘ rotation a) z) =
        ∫ z in U, euclideanGradientEnergy v z := by
  have hm := (rotation a).measurePreserving.restrict_preimage_emb
    (rotation a).toMeasurableEquiv.measurableEmbedding U
  have hc : IntegrableOn (euclideanGradientEnergy v ∘ rotation a) (rotation a ⁻¹' U) :=
    (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : euclideanGradientEnergy (v ∘ rotation a) =ᵐ[volume.restrict (rotation a ⁻¹' U)]
      euclideanGradientEnergy v ∘ rotation a := by
    filter_upwards [ae_restrict_mem (hU.preimage (rotation a).continuous).measurableSet] with z hz
    exact euclideanGradientEnergy_rotation a
      ((hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  refine ⟨hc.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  exact (rotation a).measurePreserving.setIntegral_preimage_emb
    (rotation a).toMeasurableEquiv.measurableEmbedding (euclideanGradientEnergy v) U

end CircleDomainRigidity

end

end OAI
