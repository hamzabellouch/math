import OAI.Analysis.CircleDomains.Sobolev.ComplexCoareaControls

namespace OAI

/-! Coarea transfers a zero weighted Jacobian to zero length on almost
every full level; either vanishing gradient may supply the product zero. -/
open Set Function Filter MeasureTheory Bornology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_level_integral_zero_of_product_zero
    (hcoarea : PlanarSobolevCoarea)
    {v : EuclideanPlane → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V v univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hb : IsBounded E)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q)
    (hz : ∀ᵐ p ∂volume.restrict E, q p*ENNReal.ofReal ‖V p‖ = 0) :
    ∀ᵐ t ∂volume, sobolevLevelIntegral E v q t = 0 := by
  obtain ⟨hm, he⟩ := hcoarea v hv V hw hLp E hE hb q hq
  have hzero : (∫⁻ p in E, q p*ENNReal.ofReal ‖V p‖) = 0 :=
    lintegral_eq_zero_of_ae_eq_zero hz
  rw [hzero] at he
  exact (lintegral_eq_zero_iff' hm).mp he

 theorem complex_coarea_zero_product (hcoarea : PlanarSobolevCoarea)
    {v : ℂ → ℝ} (hv : Continuous v)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (Metric.ball 0 R)))
    {F : Set ℂ} (hF : IsCompact F)
    {q : EuclideanPlane → ℝ≥0∞} (hq : Measurable q)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F),
      q p*ENNReal.ofReal ‖V p‖ = 0) :
    ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, q (complexPlaneCoordinates.symm z) ∂(μH[1] : Measure ℂ)) = 0 := by
  have hFc : IsCompact (complexPlaneCoordinates ⁻¹' F) :=
    complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  have ht := sobolev_level_integral_zero_of_product_zero hcoarea
    (hv.comp complexPlaneCoordinates.continuous) hw hLp hFc.measurableSet hFc.isBounded hq hz
  simpa only [physical_complex_level_integral] using ht

end CircleDomainRigidity

end

end OAI
