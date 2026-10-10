import OAI.Analysis.CircleDomains.Transfer.ComplexHausdorffTransport
import OAI.Analysis.CircleDomains.Sobolev.CoareaL2Weight

namespace OAI

/-! The scalar coarea estimates transported to full complex-plane levels. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem physical_complex_level_integral (E : Set ℂ) (v : ℂ → ℝ)
    (q : EuclideanPlane → ℝ≥0∞) (t : ℝ) :
    sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E) (v ∘ complexPlaneCoordinates) q t =
      ∫⁻ z in E ∩ {z | v z = t}, q (complexPlaneCoordinates.symm z) ∂(μH[1] : Measure ℂ) := by
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
    complex_sobolev_level_integral E v (q ∘ complexPlaneCoordinates.symm) t

 theorem complex_coarea_finite_levels (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set ℂ} (hE : IsCompact E) :
    ∀ᵐ t ∂volume, (μH[1] : Measure ℂ) (E ∩ {z | v z = t}) < ∞ := by
  have hEc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hE
  have ht := sobolev_coarea_ae_finite_levels hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hEc.measurableSet hEc.isBounded
  filter_upwards [ht] with t ht
  have he := physical_complex_level_integral E v (fun _ => 1) t
  simp only [sobolevLevelIntegral, lintegral_one, Measure.restrict_apply_univ] at he
  rwa [← he]

 theorem complex_coarea_L2_weight_finite (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set ℂ} (hE : IsCompact E)
    {q : EuclideanPlane → ℝ} (hq : Measurable q)
    (hL : MemLp q 2 (volume.restrict (complexPlaneCoordinates ⁻¹' E))) :
    ∀ᵐ t ∂volume,
      (∫⁻ z in E ∩ {z | v z = t}, ENNReal.ofReal ‖q (complexPlaneCoordinates.symm z)‖
        ∂(μH[1] : Measure ℂ)) < ∞ := by
  have hEc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hE
  have ht := coarea_L2_weight_finite hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hEc.measurableSet hEc.isBounded hq hL
  change ∀ᵐ t ∂volume, sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E)
    (v ∘ complexPlaneCoordinates) (fun p => ENNReal.ofReal ‖q p‖) t < ∞ at ht
  simpa only [physical_complex_level_integral] using ht

 theorem complex_coarea_L2_errors (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set ℂ} (hE : IsCompact E)
    (f : ℕ → EuclideanPlane → ℝ) (hf : ∀ n, Measurable (f n))
    (hL : ∀ n, MemLp (f n) 2 (volume.restrict (complexPlaneCoordinates ⁻¹' E)))
    (hs : Summable (fun n => (eLpNorm (f n) 2
      (volume.restrict (complexPlaneCoordinates ⁻¹' E))).toReal)) :
    ∀ᵐ t ∂volume, Tendsto (fun n =>
      ∫⁻ z in E ∩ {z | v z = t}, ENNReal.ofReal ‖f n (complexPlaneCoordinates.symm z)‖
        ∂(μH[1] : Measure ℂ)) atTop (𝓝 0) := by
  have hEc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hE
  have ht := coarea_L2_errors hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hEc.measurableSet hEc.isBounded f hf hL hs
  change ∀ᵐ t ∂volume, Tendsto (fun n => sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' E)
    (v ∘ complexPlaneCoordinates) (fun p => ENNReal.ofReal ‖f n p‖) t) atTop (𝓝 0) at ht
  simpa only [physical_complex_level_integral] using ht

 theorem complex_coarea_zero_weight (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {F : Set ℂ} (hF : IsCompact F)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q) :
    ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, q (complexPlaneCoordinates.symm z) ∂(μH[1] : Measure ℂ)) = 0 := by
  have hFc := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  have ht := sobolev_level_integral_zero_of_gradient_zero hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hFc.measurableSet hFc.isBounded hz hq
  change ∀ᵐ t ∂volume, sobolevLevelIntegral (complexPlaneCoordinates ⁻¹' F)
    (v ∘ complexPlaneCoordinates) q t = 0 at ht
  simpa only [physical_complex_level_integral] using ht

end CircleDomainRigidity

end

end OAI
