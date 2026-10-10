import OAI.Analysis.LipschitzHilbert.Fourier.PlanarSliceFourierBasic

namespace OAI

/-!
# Fourier support of affine-line restrictions

Fubini and the area-preserving shear identify the transverse Fourier
transform of a slice coefficient with the planar transform on the fiber
`ξ+sη=ω`. One-dimensional Fourier inversion then proves exact vanishing
when this fiber misses the planar spectrum. No tensor representation is used.
-/

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

private theorem planar_phase_integrable (f : SchwartzMap (ℝ × ℝ) ℂ)
    (s ω η : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.fourierChar (-(z.1 * ω + z.2 * η)) •
      f (z.1, z.2 + s * z.1)) (volume.prod volume) := by
  apply (planar_shear_integrable f s).norm.mono'
  · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [Circle.norm_smul]
    exact le_rfl

theorem planarSliceFourier_fourier (f : SchwartzMap (ℝ × ℝ) ℂ) (s ω η : ℝ) :
    𝓕 (planarSliceFourier f s ω) η = planarFourier f (ω - s * η, η) := by
  rw [Real.fourier_eq]
  simp only [Real.inner_apply]
  have hinter (b : ℝ) : Real.fourierChar (-(b * η)) • planarSliceFourier f s ω b =
      ∫ x, Real.fourierChar (-(x * ω + b * η)) • f (x, b + s * x) := by
    rw [planarSliceFourier_eq]
    change (Real.fourierChar (-(b * η)) : ℂ) •
      (∫ x, Real.fourierChar (-(x * ω)) • f (x, b + s * x)) = _
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with x
    change Real.fourierChar (-(b * η)) •
      (Real.fourierChar (-(x * ω)) • f (x, b + s * x)) = _
    rw [← mul_smul, ← Real.fourierChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hinter]
  rw [← integral_prod_symm _ (planar_phase_integrable f s ω η)]
  have hshear := (slopeShear_measurePreserving s).integral_comp
    (slopeShear s).measurableEmbedding
    (fun z : ℝ × ℝ => Real.fourierChar (-(z.1 * (ω - s * η) + z.2 * η)) • f z)
  calc
    _ = ∫ z, Real.fourierChar (-((slopeShear s z).1 * (ω - s * η) +
        (slopeShear s z).2 * η)) • f (slopeShear s z) ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      change Real.fourierChar (-(z.1 * ω + z.2 * η)) • f (z.1, z.2 + s * z.1) =
        Real.fourierChar (-(z.1 * (ω - s * η) + (z.2 + s * z.1) * η)) •
          f (z.1, z.2 + s * z.1)
      congr 2
      ring
    _ = _ := hshear

/-- A frequency fiber missing the planar spectrum gives exact vanishing
of every affine slice Fourier coefficient at that frequency. -/
theorem planarSchwartzSlice_fourier_eq_zero (f : SchwartzMap (ℝ × ℝ) ℂ)
    (b s ω : ℝ) (hfiber : ∀ η, planarFourier f (ω - s * η, η) = 0) :
    𝓕 (planarSchwartzSlice f b s) ω = 0 := by
  have hzero : 𝓕 (planarSliceFourier f s ω) = (0 : ℝ → ℂ) := by
    funext η
    simp only [planarSliceFourier_fourier, hfiber, Pi.zero_apply]
  have h := (planarSliceFourier_continuous f s ω).fourierInv_fourier_eq
    (planarSliceFourier_integrable f s ω) (by rw [hzero]; exact integrable_zero _ _ _)
  have hb := congrFun h b
  rw [hzero] at hb
  simpa only [Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero,
    planarSliceFourier] using hb.symm

end LipschitzHilbert

end

end OAI
